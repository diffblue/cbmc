/* FUNCTION: fegetround */

#include <fenv.h>

extern int __CPROVER_rounding_mode;

int fegetround(void)
{
__CPROVER_HIDE:;
  // CPROVER uses the x86 numbering of the rounding modes
  return
         #ifdef FE_DOWNWARD
         __CPROVER_rounding_mode==1?FE_DOWNWARD:
         #endif
         __CPROVER_rounding_mode==0?FE_TONEAREST:
         __CPROVER_rounding_mode==3?FE_TOWARDZERO:
         #ifdef FE_UPWARD
         __CPROVER_rounding_mode==2?FE_UPWARD:
         #endif
         -1;
}

/* FUNCTION: fesetround */

#include <fenv.h>

int fesetround(int rounding_mode)
{
__CPROVER_HIDE:;
  // CPROVER uses the x86 numbering of the rounding modes
  __CPROVER_rounding_mode=
    #ifdef FE_DOWNWARD
    rounding_mode==FE_DOWNWARD?1:
    #endif
    rounding_mode==FE_TONEAREST?0:
    rounding_mode==FE_TOWARDZERO?3:
    #ifdef FE_UPWARD
    rounding_mode==FE_UPWARD?2:
    #endif
    0;
  return 0; // we never fail
}
