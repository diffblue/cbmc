/* FUNCTION: fegetround */

inline int fegetround(void)
{
__CPROVER_hide:
  return __CPROVER_rounding_mode;
}

/* FUNCTION: fesetround */

inline int fesetround(int rounding_mode)
{
__CPROVER_hide:
  __CPROVER_rounding_mode=rounding_mode;
  return 0; // we never fail
}
