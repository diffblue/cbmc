
/* FUNCTION: longjmp */

#ifndef __CPROVER_SETJMP_H_INCLUDED
#include <setjmp.h>
#define __CPROVER_SETJMP_H_INCLUDED
#endif

inline void longjmp(jmp_buf env, int val)
{
  // does not return
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
  __CPROVER_assume(0);
}
       
              
