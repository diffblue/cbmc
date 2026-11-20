#include <assert.h>
#include <math.h>

int main()
{
  // IEEE 754 remainder: x - n*y where n = round_to_nearest_even(exact(x/y))
  // Here exact(0.5 / (1.0f/3)) is slightly below 1.5 (since 1.0f/3 rounds up).
  // So n should be 1 (nearest integer below 1.5), giving a positive result.
  // Bug: fp division gives exactly 1.5, rint(1.5)=2 (even), wrong sign.
  float x = 0x1p-1f;
  float y = 0x1.555556p-2f;
  float result = remainderf(x, y);
  assert(result > 0.0f);
}
