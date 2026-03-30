// IEEE 754 FMA special cases
#include <assert.h>
#include <math.h>

int main()
{
  // fma(NaN, y, z) = NaN
  assert(isnan(fmaf(NAN, 1.0f, 0.0f)));

  // fma(x, NaN, z) = NaN
  assert(isnan(fmaf(1.0f, NAN, 0.0f)));

  // fma(x, y, NaN) = NaN
  assert(isnan(fmaf(1.0f, 1.0f, NAN)));

  // fma(0, inf, z) = NaN (0 * inf is undefined)
  assert(isnan(fmaf(0.0f, INFINITY, 1.0f)));

  // fma(inf, 0, z) = NaN
  assert(isnan(fmaf(INFINITY, 0.0f, 1.0f)));

  // fma(inf, x, -inf) = NaN when inf*x = +inf (inf + (-inf) is undefined)
  assert(isnan(fmaf(INFINITY, 1.0f, -INFINITY)));

  // fma(inf, x, z) = +inf for finite z
  assert(isinf(fmaf(INFINITY, 2.0f, 3.0f)));

  // fma(x, y, inf) = +inf for finite x*y
  assert(isinf(fmaf(2.0f, 3.0f, INFINITY)));

  return 0;
}
