// fmaf should compute x*y+z with a single rounding.
// The C library model used to do x*y then +z (two roundings).
// Example: fmaf(1+eps, 1+eps, -(1+2*eps)) where eps = 2^-23
// Exact result: eps^2 = 2^-46 > 0
// Double rounding: (1+eps)*(1+eps) rounds to 1+2*eps, then +c = 0
// True FMA: should give eps^2 which is > 0
#include <assert.h>
#include <math.h>

int main()
{
  float a = 1.0f + 1.1920929e-7f;    // 1 + 2^-23
  float c = -(1.0f + 2.3841858e-7f); // -(1 + 2^-22)
  float r = fmaf(a, a, c);
  assert(r > 0.0f);
  return 0;
}
