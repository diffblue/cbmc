// sqrtf must honour the current rounding mode.
#include <assert.h>
#include <fenv.h>
#include <math.h>

int main()
{
  // sqrt(2) lies between 0x1.6a09e6p+0f and 0x1.6a09e8p+0f, closer to the
  // former.
  fesetround(FE_TOWARDZERO);
  float r_tz = sqrtf(2.0f);
  fesetround(FE_UPWARD);
  float r_up = sqrtf(2.0f);
  fesetround(FE_TONEAREST);
  float r_ne = sqrtf(2.0f);

  assert(r_tz == 0x1.6a09e6p+0f);
  assert(r_ne == 0x1.6a09e6p+0f);
  assert(r_up == 0x1.6a09e8p+0f);
  return 0;
}
