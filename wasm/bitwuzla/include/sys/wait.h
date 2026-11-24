/* WASI cannot start processes. CaDiCaL only does so to read compressed files, which
   bitwuzla never asks it to, so these are declared here and fail in wasi_stubs.c. */
#ifndef HEVM_WASI_SYS_WAIT_H
#define HEVM_WASI_SYS_WAIT_H

#include <stdio.h>
#include <sys/types.h>

#ifdef __cplusplus
extern "C" {
#endif

pid_t waitpid (pid_t pid, int *status, int options);
pid_t fork (void);
int pipe (int fds[2]);
int execv (const char *path, char *const argv[]);
FILE *popen (const char *command, const char *mode);
int pclose (FILE *stream);
int dup2 (int oldfd, int newfd);

#ifdef __cplusplus
}
#endif

#endif
