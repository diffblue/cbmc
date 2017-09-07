
/* FUNCTION: longjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

inline void longjmp(jmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assume(0);
}

/* FUNCTION: _longjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

inline void _longjmp(jmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assume(0);
}

/* FUNCTION: siglongjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

inline void siglongjmp(sigjmp_buf env, int val)
{
  // does not return
  (void)env;
  (void)val;
  __CPROVER_assume(0);
}

/* FUNCTION: setjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

int __VERIFIER_nondet_int();

inline int setjmp(jmp_buf env)
{
  // store PC
  int retval=__VERIFIER_nondet_int();
  (void)env;
  return retval;
}
