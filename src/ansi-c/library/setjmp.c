#ifdef LIBRARY_CHECK
#include <setjmp.h>
#endif

/* FUNCTION: longjmp */

inline void longjmp(jmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assume(0);
}

/* FUNCTION: _longjmp */

inline void _longjmp(jmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assume(0);
}

/* FUNCTION: siglongjmp */

inline void siglongjmp(sigjmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assume(0);
}

/* FUNCTION: setjmp */

int __VERIFIER_nondet_int();

inline int setjmp(jmp_buf env)
{
  // store PC
  int retval=__VERIFIER_nondet_int();
  (void)env;
  return retval;
}
