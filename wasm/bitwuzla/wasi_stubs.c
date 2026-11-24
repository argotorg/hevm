#include <errno.h>
#include <sys/wait.h>

pid_t waitpid (pid_t pid, int *status, int options) { errno = ENOSYS; return -1; }
pid_t fork (void) { errno = ENOSYS; return -1; }
int pipe (int fds[2]) { errno = ENOSYS; return -1; }
int execv (const char *path, char *const argv[]) { errno = ENOSYS; return -1; }
FILE *popen (const char *command, const char *mode) { errno = ENOSYS; return NULL; }
int pclose (FILE *stream) { errno = ENOSYS; return -1; }
int dup2 (int oldfd, int newfd) { errno = ENOSYS; return -1; }
