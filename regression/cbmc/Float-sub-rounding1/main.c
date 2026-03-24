// Based on Z3#7162: Subtraction with different rounding modes.
// IEEE 754: x - x == +0 for all rounding modes except
// round-toward-negative, where x - x == -0.
// In C, the default rounding mode is round-to-nearest-ties-to-even.

#include <assert.h>
#include <fenv.h>
#include <math.h>

int main()
{
  double x;

  // Assume x is finite (not NaN or Inf, since Inf - Inf = NaN)
  __CPROVER_assume(!isnan(x) && !isinf(x));

  double result = x - x;

  // x - x must be zero
  assert(result == 0.0);

  // With default rounding (RNE), x - x == +0.0
  assert(!signbit(result));

  return 0;
}
