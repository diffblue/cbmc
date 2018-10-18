// gcc -Wall -W -lm double-to-float-with-rounding-modes.c -o double-to-float-with-rounding-modes -frounding-math -fsignaling-nans -ffp-contract=off -msse2 -mfpmath=sse

#ifdef __GNUC__
#include <assert.h>
#include <fenv.h>
#include <math.h>

float setRoundingModeAndCast(int mode, double d)
{
  fesetround(mode);
  return (float)d;
}

void test(int mode, double d, float result)
{
  float f = setRoundingModeAndCast(mode, d);
  assert(f == result);
  return;
}
#endif

int main(void)
{
#ifdef __GNUC__
  test(FE_TONEAREST, 0x1.fffffffffffffp+1023, +INFINITY);
#endif

  return 1;
}
