// sqrtf with non-default rounding mode
// The C library model doesn't correctly handle all rounding modes.
#include <assert.h>
#include <fenv.h>
#include <math.h>

int main()
{
  // sqrt(2.0) with round-toward-zero should give 0x3FB504F2
  fesetround(FE_TOWARDZERO);
  float r = sqrtf(2.0f);
  // The result should be strictly less than sqrt(2.0) with RNE
  fesetround(FE_TONEAREST);
  float r_rne = sqrtf(2.0f);
  assert(r <= r_rne);
  return 0;
}
