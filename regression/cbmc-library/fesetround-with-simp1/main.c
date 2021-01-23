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
  // 0x1.fffffep+127f is the largest binary32 float so
  // these should all be representable as floats...
  test(FE_TONEAREST, 0x1.fffffep+127, 0x1.fffffep+127);
#ifdef FE_UPWARD
  test(FE_UPWARD, 0x1.fffffep+127, 0x1.fffffep+127);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, 0x1.fffffep+127, 0x1.fffffep+127);
#endif
  test(FE_TOWARDZERO, 0x1.fffffep+127, 0x1.fffffep+127);

  // Likewise, this should be an obvious sanity check
  test(FE_TONEAREST, +INFINITY, +INFINITY);
#ifdef FE_UPWARD
  test(FE_UPWARD, +INFINITY, +INFINITY);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, +INFINITY, +INFINITY);
#endif
  test(FE_TOWARDZERO, +INFINITY, +INFINITY);

  // Nearer to 0x1.fffffep+127 than to 0x1.000000p+128
  test(FE_TONEAREST, 0x1.fffffe0000001p+127, 0x1.fffffep+127);
#ifdef FE_UPWARD
  test(FE_UPWARD, 0x1.fffffe0000001p+127, +INFINITY);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, 0x1.fffffe0000001p+127, 0x1.fffffep+127);
#endif
  test(FE_TOWARDZERO, 0x1.fffffe0000001p+127, 0x1.fffffep+127);

  // 0x1.fffffefffffffp+127 is immediately below half way
  test(FE_TONEAREST, 0x1.fffffefffffffp+127, 0x1.fffffep+127);
#ifdef FE_UPWARD
  test(FE_UPWARD, 0x1.fffffefffffffp+127, +INFINITY);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, 0x1.fffffefffffffp+127, 0x1.fffffep+127);
#endif
  test(FE_TOWARDZERO, 0x1.fffffefffffffp+127, 0x1.fffffep+127);

  // Half way
  test(FE_TONEAREST, 0x1.ffffffp+127, +INFINITY);
#ifdef FE_UPWARD
  test(FE_UPWARD, 0x1.ffffffp+127, +INFINITY);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, 0x1.ffffffp+127, 0x1.fffffep+127);
#endif
  test(FE_TOWARDZERO, 0x1.ffffffp+127, 0x1.fffffep+127);

  // Larger
  test(FE_TONEAREST, 0x1.0p+128, +INFINITY);
#ifdef FE_UPWARD
  test(FE_UPWARD, 0x1.0p+128, +INFINITY);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, 0x1.0p+128, 0x1.fffffep+127);
#endif
  test(FE_TOWARDZERO, 0x1.0p+128, 0x1.fffffep+127);

  // Huge
  test(FE_TONEAREST, 0x1.fffffffffffffp+1023, +INFINITY);
#ifdef FE_UPWARD
  test(FE_UPWARD, 0x1.fffffffffffffp+1023, +INFINITY);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, 0x1.fffffffffffffp+1023, 0x1.fffffep+127);
#endif
  test(FE_TOWARDZERO, 0x1.fffffffffffffp+1023, 0x1.fffffep+127);

  // Same again but negative
  test(FE_TONEAREST, -0x1.fffffep+127, -0x1.fffffep+127);
#ifdef FE_UPWARD
  test(FE_UPWARD, -0x1.fffffep+127, -0x1.fffffep+127);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, -0x1.fffffep+127, -0x1.fffffep+127);
#endif
  test(FE_TOWARDZERO, -0x1.fffffep+127, -0x1.fffffep+127);

  test(FE_TONEAREST, -INFINITY, -INFINITY);
#ifdef FE_UPWARD
  test(FE_UPWARD, -INFINITY, -INFINITY);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, -INFINITY, -INFINITY);
#endif
  test(FE_TOWARDZERO, -INFINITY, -INFINITY);

  test(FE_TONEAREST, -0x1.fffffe0000001p+127, -0x1.fffffep+127);
#ifdef FE_UPWARD
  test(FE_UPWARD, -0x1.fffffe0000001p+127, -0x1.fffffep+127);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, -0x1.fffffe0000001p+127, -INFINITY);
#endif
  test(FE_TOWARDZERO, -0x1.fffffe0000001p+127, -0x1.fffffep+127);

  test(FE_TONEAREST, -0x1.fffffefffffffp+127, -0x1.fffffep+127);
#ifdef FE_UPWARD
  test(FE_UPWARD, -0x1.fffffefffffffp+127, -0x1.fffffep+127);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, -0x1.fffffefffffffp+127, -INFINITY);
#endif
  test(FE_TOWARDZERO, -0x1.fffffefffffffp+127, -0x1.fffffep+127);

  test(FE_TONEAREST, -0x1.ffffffp+127, -INFINITY);
#ifdef FE_UPWARD
  test(FE_UPWARD, -0x1.ffffffp+127, -0x1.fffffep+127);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, -0x1.ffffffp+127, -INFINITY);
#endif
  test(FE_TOWARDZERO, -0x1.ffffffp+127, -0x1.fffffep+127);

  test(FE_TONEAREST, -0x1.0p+128, -INFINITY);
#ifdef FE_UPWARD
  test(FE_UPWARD, -0x1.0p+128, -0x1.fffffep+127);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, -0x1.0p+128, -INFINITY);
#endif
  test(FE_TOWARDZERO, -0x1.0p+128, -0x1.fffffep+127);

  test(FE_TONEAREST, -0x1.fffffffffffffp+1023, -INFINITY);
#ifdef FE_UPWARD
  test(FE_UPWARD, -0x1.fffffffffffffp+1023, -0x1.fffffep+127);
#endif
#ifdef FE_DOWNWARD
  test(FE_DOWNWARD, -0x1.fffffffffffffp+1023, -INFINITY);
#endif
  test(FE_TOWARDZERO, -0x1.fffffffffffffp+1023, -0x1.fffffep+127);
#endif

  return 1;
}
