// Based on Z3#7162 and CVC5#11139: Fused multiply-add.
// Test that CBMC handles fmaf correctly.
// fma(a, b, c) = a*b + c with a single rounding.

#include <assert.h>
#include <math.h>

int main()
{
  // fma(2.0, 3.0, 4.0) = 2*3 + 4 = 10.0
  float r1 = fmaf(2.0f, 3.0f, 4.0f);
  assert(r1 == 10.0f);

  // fma with NaN input produces NaN
  float r2 = fmaf(NAN, 1.0f, 0.0f);
  assert(isnan(r2));

  // fma(0, inf, x) is NaN (0 * inf is NaN)
  float r3 = fmaf(0.0f, INFINITY, 1.0f);
  assert(isnan(r3));

  return 0;
}
