// Based on Z3#6728: NaN propagation through operations.
// In IEEE 754, any arithmetic operation with NaN produces NaN.
// This test verifies CBMC correctly handles NaN propagation.

#include <assert.h>
#include <math.h>

int main()
{
  float x;

  // NaN + anything = NaN
  float r1 = x + NAN;
  assert(isnan(r1));

  // NaN - anything = NaN
  float r2 = x - NAN;
  assert(isnan(r2));

  // NaN * anything = NaN
  float r3 = x * NAN;
  assert(isnan(r3));

  // NaN / anything = NaN
  float r4 = x / NAN;
  assert(isnan(r4));

  return 0;
}
