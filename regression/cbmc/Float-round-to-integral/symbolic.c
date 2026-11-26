// Compare round-to-integral of an arbitrary value in an arbitrary rounding
// mode with a reference that is computed exactly via integer arithmetic.

#include <assert.h>

// BIG is 2^f: values of at least this magnitude are integral
#if defined(DOUBLE)
#  define FT double
#  define BIG 0x1p52
#elif defined(SMALL)
// a 3-bit exponent, in which the largest finite value, 15.75, rounds up to
// infinity
#  define FT __CPROVER_floatbv[10][6]
#  define BIG 64
#else
#  define FT float
#  define BIG 0x1p23f
#endif

extern int __CPROVER_rounding_mode;

int main()
{
  FT x;
  int rm;
  __CPROVER_assume(rm >= 0 && rm <= 4);
  FT r = __CPROVER_round_to_integralf(x, rm);

  // the reference computation does not round
  __CPROVER_rounding_mode = 0;

  if(x != x)
  {
    assert(r != r);
    return 0;
  }

  // the sign is preserved, also for zeros
  assert(__CPROVER_signf(r) == __CPROVER_signf(x));

  const FT abs_x = x < 0 ? -x : x;
  if(abs_x >= BIG)
  {
    // already integral, or infinite
    assert(r == x);
    return 0;
  }

  // integral part and fractional part, both exact
  const long long i = (long long)x;
  const FT t = (FT)i;
  const FT frac = x - t;
  const FT abs_frac = frac < 0 ? -frac : frac;
  const FT away = x < 0 ? t - 1 : t + 1;

  FT expected = t;
  if(rm == 0) // to nearest, ties to even
  {
    if(abs_frac > (FT)0.5 || (abs_frac == (FT)0.5 && i % 2 != 0))
      expected = away;
  }
  else if(rm == 1) // downward
  {
    if(frac < 0)
      expected = t - 1;
  }
  else if(rm == 2) // upward
  {
    if(frac > 0)
      expected = t + 1;
  }
  else if(rm == 4) // to nearest, ties away from zero
  {
    if(abs_frac >= (FT)0.5)
      expected = away;
  }

  assert(r == expected);
  return 0;
}
