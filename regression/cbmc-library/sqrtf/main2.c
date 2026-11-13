#include <assert.h>
#include <fenv.h>
#include <float.h>
#include <math.h>

int main(void)
{
  // IEEE 754 squareRoot is correctly rounded (C11 F.10.4.5)
  float x = 1.0f + FLT_EPSILON;
  assert(sqrtf(x) == 1.0f);

  float y = 2.0f;
  fesetround(FE_DOWNWARD);
  assert(sqrtf(y) == 0x1.6a09e6p+0f);
  fesetround(FE_UPWARD);
  assert(sqrtf(y) == 0x1.6a09e8p+0f);

  return 0;
}
