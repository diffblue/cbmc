/* FUNCTION: fegetround */

#include <fenv.h>

extern int __CPROVER_rounding_mode;

inline int fegetround(void)
{
__CPROVER_HIDE:;
  // CPROVER uses the x86 numbering of the rounding modes
  return __CPROVER_rounding_mode==FE_DOWNWARD?1:
         __CPROVER_rounding_mode==FE_TONEAREST?0:
         __CPROVER_rounding_mode==FE_TOWARDZERO?3:
         __CPROVER_rounding_mode==FE_UPWARD?2:
         -1;
}

/* FUNCTION: fesetround */

#include <fenv.h>

inline int fesetround(int rounding_mode)
{
__CPROVER_HIDE:;
  // CPROVER uses the x86 numbering of the rounding modes
  __CPROVER_rounding_mode=
    rounding_mode==FE_DOWNWARD?1:
    rounding_mode==FE_TONEAREST?0:
    rounding_mode==FE_TOWARDZERO?3:
    rounding_mode==FE_UPWARD?2:
    0;
  return 0; // we never fail
}
