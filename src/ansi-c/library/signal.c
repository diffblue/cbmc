/* FUNCTION: kill */

#ifndef __CPROVER_SYS_TYPES_H_INCLUDED
#include <sys/types.h>
#define __CPROVER_SYS_TYPES_H_INCLUDED
#endif

#ifndef __CPROVER_SIGNAL_H_INCLUDED
#include <signal.h>
#define __CPROVER_SIGNAL_H_INCLUDED
#endif

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

int kill(pid_t pid, int sig)
{
  (void)pid;
  (void)sig;
  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  return error ? -1 : 0;
}
