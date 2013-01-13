#include <assert.h>
#include <math.h>
#include <fenv.h>

float nondet_value();

// Should work without this as it defaults to off.
// It is explicitly ignored by GCC
#pragma STDC FENV_ACCESS OFF

void roundingTest (float f1, float f2) {
  // (Re)Set to the default rounding mode.
  fesetround(FE_TONEAREST);

 // With round to nearest, should get 0x1.000002p+0f
  float roundToNearestSum = f1 + f2;
  assert(roundToNearestSum == 0x1.000002p+0f);

  // Change the rounding mode
  fesetround(FE_DOWNWARD);

  // Should now round down to 0x1p+0;
  float roundDownSum = f1 + f2;
  assert(roundDownSum == 0x1.0p+0f);

  return;
}

int main (void) {
  float f1 = 0x1.0p+0;
  float f2 = 0x1.8p-24;

  // Test with constant folding
  roundingTest(f1,f2);

  // Test with bitwise model
  float f3 = nondet_value();
  float f4 = nondet_value();

  assume((0x1.fffffep-1f < f3) && (f3 < 0x1.000002p+0f));
  assume((0x1.7ffffep-24f < f4) && (f4 < 0x1.800002p-24f));

  roundingTest(f3,f4);

  return 0;
}
