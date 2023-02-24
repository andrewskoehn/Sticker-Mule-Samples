/*
 * cush - the customizable shell.
 *
 * Developed by Andrew Koehn
 * Feb. 2021
 * 
 */
#include <stdio.h>
#include <readline/readline.h>
#include <unistd.h>
#include <stdlib.h>
#include <termios.h>
#include <sys/wait.h>
#include <assert.h>
#include <fcntl.h>

/* Libraries have a number of unused functions. */
#pragma GCC diagnostic ignored "-Wunused-function"

#include "termstate_management.h"
#include "signal_support.h"
#include "shell-ast.h"
#include "utils.h"

static void handle_child_status(pid_t pid, int status);

/* Print help message about executing the shell. */
static void
usage(char *progname)
{
    printf("Usage: %s -h\n"
        " -h            print this help\n",
        progname);

    exit(EXIT_SUCCESS);
}

static char prompt_new[50] = "";

/* Build a prompt */
static char *
build_prompt(void)
{
    return strdup(prompt_new);
}

enum job_status {
    FOREGROUND,     /* job is running in foreground.  Only one job can be
                       in the foreground state. */
    BACKGROUND,     /* job is running in background */
    STOPPED,        /* job is stopped via SIGSTOP */
    NEEDSTERMINAL,  /* job is stopped because it was a background job
                       and requires exclusive terminal access */
};

struct job {
    struct list_elem elem;              /* Link element for jobs list. */
    struct ast_pipeline *pipe;          /* The pipeline of commands this job represents */
    int     jid;                        /* Job id. */
    enum job_status status;             /* Job status. */ 
    int  num_processes_alive;           /* The number of processes that we know to be alive */
    struct termios saved_tty_state;     /* The state of the terminal when this job was 
                                           stopped after having been in foreground */

    struct list/* <process_info> */ processes;  /* List holding the process info for each process in the job */
    pid_t pgid;                                 /* Process group id for this job */
    bool status_changed;                        /* Track if a job's status changed since the last check */
    bool exit_normal;                           /* Track if a job exits/finishes normally */
};

struct process_info {
    pid_t pid;              /* Process PID */
    int term_sig;           /* Signal identifier for process's terminating signal */
    struct list_elem elem;  /* Link element for each job's processes list */
};

/* Utility functions for job list management.
 * Use 2 data structures: 
 * (a) an array jid2job to quickly find a job based on its id
 * (b) a linked list to support iteration
 */
#define MAXJOBS (1<<16)
static struct list job_list;

static struct job * jid2job[MAXJOBS];

/* Return job corresponding to jid */
static struct job * 
get_job_from_jid(int jid)
{
    if (jid > 0 && jid < MAXJOBS && jid2job[jid] != NULL)
        return jid2job[jid];

    return NULL;
}

/* Add a new job to the job list */
static struct job *
add_job(struct ast_pipeline *pipe)
{
    struct job * job = malloc(sizeof *job);
    
    // inits the process list we added
    list_init(&job->processes);
    
    job->pipe = pipe;
    job->num_processes_alive = 0;
    list_push_back(&job_list, &job->elem);
    for (int i = 1; i < MAXJOBS; i++) {
        if (jid2job[i] == NULL) {
            jid2job[i] = job;
            job->jid = i;
            return job;
        }
    }
    fprintf(stderr, "Maximum number of jobs exceeded\n");
    abort();
    return NULL;
}

/* Delete a job.
 * This is called only when all processes that were
 * forked for this job are known to have terminated.
 */
static void
delete_job(struct job *job)
{
    int jid = job->jid;
    assert(jid != -1);
    jid2job[jid]->jid = -1;
    jid2job[jid] = NULL;

    struct list_elem * proc_index;
    for(proc_index = list_begin(&job->processes); proc_index != list_end(&job->processes);) {
        struct process_info * proc_info = list_entry(proc_index, struct process_info, elem);
        proc_index = list_next(proc_index);
        free(proc_info);
    }

    ast_pipeline_free(job->pipe);

    free(job);
}

static const char *
get_status(enum job_status status)
{
    switch (status) {
    case FOREGROUND:
        return "Foreground";
    case BACKGROUND:
        return "Running";
    case STOPPED:
        return "Stopped";
    case NEEDSTERMINAL:
        return "Stopped (tty)";
    default:
        return "Unknown";
    }
}

/* Print the command line that belongs to one job. */
static void
print_cmdline(struct ast_pipeline *pipeline)
{
    struct list_elem * e = list_begin (&pipeline->commands); 
    for (; e != list_end (&pipeline->commands); e = list_next(e)) {
        struct ast_command *cmd = list_entry(e, struct ast_command, elem);
        if (e != list_begin(&pipeline->commands))
            printf("| ");
        char **p = cmd->argv;
        printf("%s", *p++);
        while (*p)
            printf(" %s", *p++);
    }
}

/* Print a job */
static void
print_job(struct job *job)
{
    printf("[%d]\t%s\t\t(", job->jid, get_status(job->status));
    print_cmdline(job->pipe);
    printf(")\n");
}

/*
 * sigchld_handler()
 *
 * Call waitpid() to learn about any child processes that
 * have exited or changed status (been stopped, needed the
 * terminal, etc.)
 * 
 * Record the information by updating the job list
 * data structures.  Since the call may be spurious (e.g.
 * an already pending SIGCHLD is delivered even though
 * a foreground process was already reaped), ignore when
 * waitpid returns -1.
 * 
 * Use a loop with WNOHANG since only a single SIGCHLD 
 * signal may be delivered for multiple children that have 
 * exited. All of them need to be reaped.
 */
static void
sigchld_handler(int sig, siginfo_t *info, void *_ctxt)
{
    pid_t child;
    int status;

    assert(sig == SIGCHLD);

    while ((child = waitpid(-1, &status, WUNTRACED|WNOHANG)) > 0) {
        if(child == -1)
            utils_fatal_error("waitpid failed:");
        handle_child_status(child, status);
    }
}

/* Wait for all processes in this job to complete, or for
 * the job no longer to be in the foreground.
 * 
 * Call this function from a) where waiting for
 * jobs started without the &; and b) where implementing the
 * 'fg' command.
 * 
 * handle_child_status records the information
 * obtained from waitpid() for pid 'child.'
 *
 * If a process exited, it must find the job to which it
 * belongs and decrement num_processes_alive.
 *
 * Note it is not safe to call delete_job in
 * handle_child_status because wait_for_job assumes that
 * even jobs with no more num_processes_alive haven't been
 * deallocated. Postpone deleting completed jobs
 * from the job list until when the code will no
 * longer touch them.
 *
 * The code below relies on `job->status` having been set to FOREGROUND
 * and `job->num_processes_alive` having been set to the number of
 * processes successfully forked for this job.
 */
static void
wait_for_job(struct job *job)
{
    assert(signal_is_blocked(SIGCHLD));

    while (job->status == FOREGROUND && job->num_processes_alive > 0) {
        int status;

        pid_t child = waitpid(-1, &status, WUNTRACED);

        /* When called here, any error returned by waitpid indicates a logic
         * bug in the shell. Since SIGCHLD is blocked, there cannot be races
         * where a child's exit was handled via the SIGCHLD signal handler.
         */
        if (child != -1)
            handle_child_status(child, status);
        else
            utils_fatal_error("waitpid failed, see code for explanation");
    }
}

/* Update the bookkeeping for each job's processes list
 * when a child process changes state; distinguishes
 * between exiting normally, being signaled, and stopping.
 */
static void
handle_child_status(pid_t pid, int status)
{
    assert(signal_is_blocked(SIGCHLD));

    // loop through jobs in job list to find the job with the pid stored
    struct list_elem * job_index;
    for(job_index = list_begin(&job_list); job_index != list_end(&job_list); job_index = list_next(job_index)) {
        struct job * job = list_entry(job_index, struct job, elem);

        // loop through process info in the job's process list
        struct list_elem * proc_index;
        for(proc_index = list_begin(&job->processes); proc_index != list_end(&job->processes); proc_index = list_next(proc_index)) {
            struct process_info * proc_info = list_entry(proc_index, struct process_info, elem);
            
            if(proc_info->pid == pid) {
                // handle processes that exit normally
                if(WIFEXITED(status)) {
                    job->num_processes_alive--;
                    if(job->num_processes_alive == 0)
                        job->exit_normal = true;
                    job->status_changed = true;
                    break;
                }
                // handle processes that are terminated because of a signal
                else if(WIFSIGNALED(status)) {
                    int sig = WTERMSIG(status);
                    proc_info->term_sig = sig;
                    job->num_processes_alive--;
                    job->status_changed = true;
                    break;
                }
                // handle processes that are stopped
                else if(WIFSTOPPED(status)) {
                    job->status = STOPPED;
                    job->status_changed = true;
                    termstate_save(&job->saved_tty_state);
                    break;
                }
            }
        }
    }
}

/* Update the bookkeeping for the jobs list when a job's status
 * changes; print information for stopped or terminated jobs
 * and for completed background jobs.
 */
static void
check_job_status_changes()
{
    /* Before new prompt is displayed, go through and clean up jobs with status changes;
     * uses a while loop with nested for loop because job deletion causes issues with for loop iteration
     * so need to break out of for loop after job delete but still want to check for remaining
     * jobs with changes (hence the while loop).
     */
    bool jobs_with_status_changes = true;
    while(jobs_with_status_changes == true && list_size(&job_list) > 0) {
        
        struct list_elem * job_index;
        for(job_index = list_begin(&job_list); job_index != list_end(&job_list); job_index = list_next(job_index)) {
            struct job * job = list_entry(job_index, struct job, elem);
            
            // handle jobs that have status changes
            if(job->status_changed == true) {

                // decide whether it is just a singular process change or if the whole job changed
                bool process_change = false;
                struct list_elem * proc_index;
                for(proc_index = list_begin(&job->processes); proc_index != list_end(&job->processes); proc_index = list_next(proc_index)) {
                    struct process_info * proc_info = list_entry(proc_index, struct process_info, elem);
                    
                    if(proc_info->term_sig == 0)
                        continue;

                    // output appropriate messages for process termination signals
                    else if(proc_info->term_sig == SIGFPE) {
                        printf("Floating point exception\n");
                        process_change = true;
                    }
                    else if(proc_info->term_sig == SIGABRT) {
                        printf("Aborted\n");
                        process_change = true;
                    }
                    else if(proc_info->term_sig == SIGTERM) {
                        printf("Terminated\n");
                        process_change = true;
                    }
                    else if(proc_info->term_sig == SIGKILL) {
                        printf("Killed\n");
                        process_change = true;
                    }
                    else if(proc_info->term_sig == SIGSEGV) {
                        printf("Segmentation fault\n");
                        process_change = true;
                    }
                }

                // handle background jobs finishing
                if(process_change == false && job->num_processes_alive == 0 && job->status == BACKGROUND) {
                    printf("[%d]     Done\n",job->jid);
                    list_remove(job_index);
                    delete_job(job);
                    termstate_sample();
                    break;
                }

                // handle jobs stopping
                else if(process_change == false && job->status == STOPPED) {
                    print_job(job);
                    job->status_changed = false;
                }
                
                // handle foreground jobs finishing
                else if(job->num_processes_alive == 0) {
                    if(job->exit_normal == true)
                        termstate_sample();
                    list_remove(job_index);
                    delete_job(job);
                    break;
                }

                else
                    job->status_changed = false;

                // keep true to force loop to continue to execute until no jobs with changes are found
                jobs_with_status_changes = true;
            }
            else
                jobs_with_status_changes = false;
        }
    }
}

/* Print the jobs list */
static void
jobs()
{
    struct list_elem * job_index;
    for(job_index = list_begin(&job_list); job_index != list_end(&job_list); job_index = list_next(job_index)){
        struct job * job = list_entry(job_index, struct job, elem);
        print_job(job);
    }
}

/* Move a stopped job to the background to continue executing */
static void
bg(struct job * job)
{
    printf("[%d] %ld\n", job->jid, (long)job->pgid);

    job->status_changed = true;
    job->status = BACKGROUND;
    if(killpg(job->pgid, SIGCONT) == -1)
        utils_error("killpg: ");
}

/* Move a stopped job or background job to the foreground
 * to continue executing; calls wait_for_job().
 */
static void           
fg(struct job * job)
{
    print_cmdline(job->pipe);
    printf("\n");
    termstate_give_terminal_to(&job->saved_tty_state, job->pgid);
    
    job->status_changed = true;
    job->status = FOREGROUND;
    if(killpg(job->pgid, SIGCONT) == -1)
        utils_error("killpg: ");

    assert(signal_is_blocked(SIGCHLD));
    wait_for_job(job);
}

// constants for pipe ends
const int READ = 0;
const int WRITE = 1;

/*** BEGIN PROGRAM ***/

int
main(int ac, char *av[])
{
    int opt;

    /* Process command-line arguments. See getopt(3) */
    while ((opt = getopt(ac, av, "h")) > 0) {
        switch (opt) {
        case 'h':
            usage(av[0]);
            break;
        }
    }

    list_init(&job_list);
    signal_set_handler(SIGCHLD, sigchld_handler);
    
    /* ignore SIGINT so shell cannot be interrupted with ctrl-c;
     * must use 'exit'
     */
    if(signal(SIGINT, SIG_IGN) == SIG_ERR)
        utils_error("signal: ");
    
    termstate_init();

    /* Read/eval loop. */
    for (;;) {

        termstate_give_terminal_back_to_shell();
        
        signal_block(SIGCHLD);
        check_job_status_changes();
        signal_unblock(SIGCHLD);

        /* Do not output a prompt unless shell's stdin is a terminal */
        char * prompt = isatty(0) ? build_prompt() : NULL;
        char * cmdline = readline(prompt);
        free(prompt);

        if (cmdline == NULL)  /* User typed EOF */
            break;

        if(strcmp(cmdline, "exit") == 0) {
            free(cmdline);
            return 0;
        }

        struct ast_command_line * cline = ast_parse_command_line(cmdline);
        free(cmdline);
        if (cline == NULL)                  /* Error in command line */
            continue;

        if (list_empty(&cline->pipes)) {    /* User hit enter */
            ast_command_line_free(cline);
            continue;
        }

        // block SIGCHLD early for safety sake
        signal_block(SIGCHLD);

        // loop through pipelines in ast_cline
        struct list_elem * pline_index;
        for(pline_index = list_begin(&cline->pipes); pline_index != list_end(&cline->pipes); pline_index = list_next(pline_index)) {
            
            // grab pipeline
            struct ast_pipeline * pline = list_entry(pline_index, struct ast_pipeline, elem);

            // used to track which job current pipeline belongs to for future commands
            int current_jid = 0;

            // initialize pipe ends
            int curr_pipe[2] = {-1, -1};
            int prev_pipe[2] = {-1, -1};

            // loop through commands in pipeline
            struct list_elem * cmd_index;
            for(cmd_index = list_begin(&pline->commands) ; cmd_index != list_end(&pline->commands); cmd_index = list_next(cmd_index)) {
                
                struct ast_command * cmd = list_entry(cmd_index, struct ast_command, elem);
                char ** args = cmd->argv;

                // check for fg built-in
                if(strcmp(args[0], "fg") == 0) {
                    // no job id given
                    if(args[1] == NULL)
                        printf("fg: job id missing\n");
                    else {
                        // check to make sure given jid references a real job
                        if(get_job_from_jid(atoi(args[1])) != NULL)
                            fg(get_job_from_jid(atoi(args[1])));   
                        else
                            printf("fg %d: no such job\n", atoi(args[1]));
                    }
                    
                    // forego creating a job and forking (PUT THIS LINE AT END OF EVERY BUILT-IN CHECK)
                    continue;
                }
                // check for jobs built-in
                else if (strcmp(args[0], "jobs") == 0) {
                    jobs();
                    continue;
                }
                // check for  bg built-in
                else if (strcmp(args[0], "bg") == 0) {
                    // no job id given
                    if(args[1] == NULL)
                        printf("bg: no job id\n");
                    // check to make sure given jid references a real job
                    else if (get_job_from_jid(atoi(args[1])) != NULL)
                    {
                        // make sure job is not already in background
                        if(get_job_from_jid(atoi(args[1]))->status ==  BACKGROUND)
                            printf("bg: %s already in background\n", args[1]);
                        else
                            bg(get_job_from_jid(atoi(args[1])));
                    }
                    else
                        printf("bg %s: no such job\n", args[1]);

                    continue;
                }
                // check for kill built-in
                else if (strcmp(args[0], "kill") == 0) {
                    if (args[1] == NULL)
                        printf("kill: no job id\n");
                    else if (get_job_from_jid(atoi(args[1])) != NULL) {
                        if(killpg(get_job_from_jid(atoi(args[1]))->pgid, SIGTERM) == -1)
                            utils_error("killpg: ");
                    }
                    else
                        printf("kill %s: no such job\n", args[1]);

                    continue;
                }
                // check for stop built-in
                else if (strcmp(args[0], "stop") == 0) {
                    if (args[1] == NULL)
                        printf("stop: no job id\n");
                    else if (get_job_from_jid(atoi(args[1])) != NULL) {
                        if(killpg(get_job_from_jid(atoi(args[1]))->pgid, SIGTSTP) == -1)
                            utils_error("killpg: ");
                    }
                    else
                        printf("stop %s: no such job\n", args[1]);

                    continue;
                }

                // make job using pipeline
                struct job * job;
                
                // add job only on first cmd of pipeline and handle other "only first command" tasks
                if(cmd_index == list_begin(&pline->commands))
                {
                    /* pointer "magic" to remove the current element and store the next element, then
                     * make the current elem the prev of the next after the removal so that
                     * the list is safe when it calls list_next on the next for loop iteration;
                     * note that the pline object is freed by deleting the job at a later point
                     */
                    struct list_elem * next = list_remove(pline_index);
                    pline_index = list_prev(next);

                    job = add_job(pline);

                    // initialize job struct variables
                    if(pline->bg_job == false)
                        job->status = FOREGROUND;
                    else
                        job->status = BACKGROUND;
                    job->pgid = 0;
                    termstate_save(&job->saved_tty_state);
                    job->status_changed = false;
                    job->exit_normal = false;
                    current_jid = job->jid;
                }
                // otherwise pull job from current job id
                else {
                    assert(current_jid != 0);
                    job = get_job_from_jid(current_jid);
                }

                // make pipe for each cmd that is not the last cmd and only if more than one cmd
                if(list_size(&pline->commands) > 1 && cmd_index != list_back(&pline->commands))
                {
                    if(pipe(curr_pipe) == -1)
                        utils_error("pipe: ");

                    // make sure no file descriptors leak into child execution
                    utils_set_cloexec(curr_pipe[READ]);
                    utils_set_cloexec(curr_pipe[WRITE]);
                }

                pid_t child = fork();
                if(child == -1)
                    utils_error("fork: ");
                
                // child process tasks
                else if(child == 0)
                {
                    // handle input redirection
                    if(pline->iored_input != NULL && cmd_index == list_begin(&pline->commands)) {
                        int fd = openat(AT_FDCWD, pline->iored_input, O_RDONLY);
                        if(fd == -1)
                            utils_error("openat: ");
                        if(dup2(fd, STDIN_FILENO) == -1)
                            utils_error("dup2: ");
                        if(close(fd) == -1)
                            utils_error("close: ");
                    }
                    
                    // handle output redirection
                    if(pline->iored_output != NULL && cmd_index == list_back(&pline->commands)) {
                        int fd;
                        // appending, not overwriting
                        if(pline->append_to_output == true) {
                            fd = openat(AT_FDCWD, pline->iored_output, O_WRONLY | O_CREAT | O_APPEND, 0666);
                            if(fd == -1)
                                utils_error("openat: ");
                        }
                        else {
                            fd = openat(AT_FDCWD, pline->iored_output, O_WRONLY | O_CREAT | O_TRUNC, 0666);
                            if(fd == -1)
                                utils_error("openat: ");
                        }
                        
                        if(dup2(fd, STDOUT_FILENO) == -1)
                            utils_error("dup2: ");
                        if(close(fd) == -1)
                            utils_error("close: ");
                        
                        // stderr redirection
                        if(cmd->dup_stderr_to_stdout == true) {
                            if(dup2(STDOUT_FILENO, STDERR_FILENO) == -1)
                                utils_error("dup2: ");
                        }
                    }

                    /* manage pipes if more than one cmd;
                     * all pipe end fds are automatically closed before executing if they
                     * haven't already been closed because their close_on_exec flag is set when
                     * they are created
                     */
                    if(list_size(&pline->commands) > 1) {
                        // handle pipe for first cmd
                        if(cmd_index == list_begin(&pline->commands)) {
                            if(dup2(curr_pipe[WRITE], STDOUT_FILENO) == -1)
                                utils_error("dup2: ");
                            if(close(curr_pipe[WRITE]) == -1)
                                utils_error("close: ");
                        }
                        // handle pipe for last cmd
                        else if(cmd_index == list_back(&pline->commands)) {
                            if(dup2(prev_pipe[READ], STDIN_FILENO) == -1)
                                utils_error("dup2: ");
                            if(close(prev_pipe[READ]) == -1)
                                utils_error("close: ");
                        }
                        // handle pipe for middle cmds
                        else {
                            if(dup2(prev_pipe[READ], STDIN_FILENO) == -1)
                                utils_error("dup2: ");
                            if(close(prev_pipe[READ]) == -1)
                                utils_error("close: ");
                            if(dup2(curr_pipe[WRITE], STDOUT_FILENO) == -1)
                                utils_error("dup2: ");
                            if(close(curr_pipe[WRITE]) == -1)
                                utils_error("close: ");
                        }

                        // stderr pipe
                        if(cmd->dup_stderr_to_stdout == true) {
                            if(dup2(STDOUT_FILENO, STDERR_FILENO) == -1)
                                utils_error("dup2: ");
                        }
                    }

                    // set correct pgids
                    if(cmd_index == list_begin(&pline->commands)) {
                        if(setpgid(0, 0) == -1)
                            utils_error("setpgid: ");

                        // give terminal control to fg process group
                        if(job->status == FOREGROUND) {
                            pid_t pgrp = getpgrp();
                            if(pgrp == -1)
                                utils_error("getpgrp: ");
                            termstate_give_terminal_to(NULL, pgrp);
                        }
                    }
                    else {
                        if(setpgid(0, job->pgid) == -1)
                            utils_error("setpgid: ");
                    }

                    // restore signals masks
                    signal_unblock(SIGCHLD);
                    signal_set_handler(SIGINT, (sa_sigaction_t) SIG_DFL);

                    // execute or handle bad executions (like mistyped commands)
                    if(execvp(args[0], args) == -1) {
                        utils_error("%s: ",args[0]);
                        ast_command_free(cmd);
                        exit(0);
                    }
                }
                
                // parent process tasks
                else {
                    // pipe file descriptor management
                    if(list_size(&pline->commands) > 1) {
                        if(cmd_index == list_begin(&pline->commands)) {
                            if(close(curr_pipe[WRITE]) == -1)
                                utils_error("close: ");
                        }
                        else if(cmd_index == list_back(&pline->commands)) {
                            if(close(prev_pipe[READ]) == -1)
                                utils_error("close: ");
                        }
                        else {
                            if(close(curr_pipe[WRITE]) == -1)
                                utils_error("close: ");
                            if(close(prev_pipe[READ]) == -1)
                                utils_error("close: ");
                        }

                        // track pipes
                        prev_pipe[READ] = curr_pipe[READ];
                        prev_pipe[WRITE] = curr_pipe[WRITE];
                    }

                    // set correct pgids
                    if(cmd_index == list_begin(&pline->commands)) {
                        job->pgid = child;
                        if(setpgid(child, job->pgid) == -1)
                            utils_error("setpgid: ");

                        // output bg job info like bash
                        if(job->status == BACKGROUND)
                            printf("[%d] %ld\n", job->jid, (long)child);
                    }
                    else {
                        if(setpgid(child, job->pgid) == -1)
                            utils_error("setpgid: ");
                    }
                    
                    // save process info to the job
                    struct process_info * pinfo = malloc(sizeof *pinfo);
                    pinfo->pid = child;
                    pinfo->term_sig = 0;
                    list_push_back(&job->processes, &pinfo->elem);
                    job->num_processes_alive++;
                }
            }

            // wait for foreground jobs to complete
            if(current_jid != 0 && get_job_from_jid(current_jid)->status == FOREGROUND) {
                assert(signal_is_blocked(SIGCHLD));
                wait_for_job(get_job_from_jid(current_jid));
            }

        }

        // memory management
        ast_command_line_free(cline);
        signal_unblock(SIGCHLD);

    }
    
    return 0;
}

/** END CODE **/