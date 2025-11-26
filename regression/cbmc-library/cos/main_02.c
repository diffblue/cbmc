#define _USE_MATH_DEFINES
#include <assert.h>
#include <math.h>

int main()
{
  // Pythagorean identity: both sin and cos in correct quadrant for π/4
  double x = M_PI / 4.0;
  double s = sin(x);
  double c = cos(x);

  // Both should be positive for first quadrant
  assert(s >= 0.0 && s <= 1.0);
  assert(c >= 0.0 && c <= 1.0);

  return 0;
}
