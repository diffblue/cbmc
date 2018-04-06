#ifdef LIBRARY_CHECK
#include <sys/types.h>
#endif

/* FUNCTION: kill */

__CPROVER_bool __VERIFIER_nondet___CPROVER_bool();

int kill(pid_t pid, int sig)
{
  (void)pid;
  (void)sig;
  __CPROVER_bool error=__VERIFIER_nondet___CPROVER_bool();
  return error ? -1 : 0;
}
