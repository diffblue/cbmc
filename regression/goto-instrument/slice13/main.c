#ifdef __GNUC__
#include <assert.h>
#include <math.h>
#include <fenv.h>

float setRoundingModeAndCast(int mode, double d) {
  fesetround(mode);
  return (float)d;
}

void test (int mode, double d, float result) {
  float f = setRoundingModeAndCast(mode,d);
  assert(f == result);
  return;
}
#endif

int main (void)
{
#ifdef __GNUC__
  // Nearer to 0x1.fffffep+127 than to 0x1.000000p+128
  test(FE_UPWARD, 0x1.fffffe0000001p+127, +INFINITY);
#endif
  return 1;
}
