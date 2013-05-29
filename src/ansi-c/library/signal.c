/* FUNCTION: kill */

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

#ifndef __CPROVER_SIGNAL_H_INCLUDED
#include <signal.h>
#define __CPROVER_SIGNAL_H_INCLUDED
#endif

int kill(pid_t pid, int sig)
{
  (void)pid;
  (void)sig;
  _Bool error;
  return error ? -1 : 0;
}
