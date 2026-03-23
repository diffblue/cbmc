#include <assert.h>
#include <math.h>

int main()
{
  // IEEE 754 remainder: n = round_to_nearest_even(exact(x/y))
  // Here exact(x/y) ≈ 5.4999999... (just below 5.5), so correct n=5.
  // Bug: fp division gives exactly 5.5, rint(5.5)=6 (even), and both
  // x-5*y and x-6*y round to the same |value| in float, so the
  // correction step cannot distinguish them without extended precision.
  float x = 0x1.d55556p+0f;
  float y = 0x1.555556p-2f;
  float result = remainderf(x, y);
  assert(result > 0.0f);
}
