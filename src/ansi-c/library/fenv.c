/* FUNCTION: fegetround */

extern int __CPROVER_rounding_mode;

inline int fegetround(void)
{
__CPROVER_HIDE:;
  return __CPROVER_rounding_mode;
}

/* FUNCTION: fesetround */

inline int fesetround(int rounding_mode)
{
__CPROVER_HIDE:;
  __CPROVER_rounding_mode=rounding_mode;
  return 0; // we never fail
}
