#define _USE_MATH_DEFINES
#include <assert.h>
#include <math.h>

int main()
{
  // sin(0) = 0 exactly
  double s = sin(0.0);
  assert(s == 0.0);

  // sin(π/2) = 1.0 in double precision (M_PI/2 is close enough)
  s = sin(M_PI / 2.0);
  assert(s >= 0.0 && s <= 1.0);

  // sin(-π/2) is in [-1, 0] (third quadrant after negation)
  s = sin(-M_PI / 2.0);
  assert(s >= -1.0 && s <= 0.0);

  // sin(π) is in [0, 1] (M_PI is at the boundary of [0, π])
  s = sin(M_PI);
  assert(s >= 0.0 && s <= 1.0);

  // Range narrowing: sin(x) >= 0 for x in [0, π]
  {
    double x;
    __CPROVER_assume(x >= 0.1 && x <= M_PI - 0.1);
    double r = sin(x);
    assert(r >= 0.0 && r <= 1.0);
  }

  // Range narrowing: sin(x) <= 0 for x in [π, 2π]
  {
    double x;
    __CPROVER_assume(x >= M_PI + 0.1 && x <= 2.0 * M_PI - 0.1);
    double r = sin(x);
    assert(r >= -1.0 && r <= 0.0);
  }

  // Range reduction: sin at large input (4π + π/4 reduces to first quadrant)
  {
    double r = sin(4.0 * M_PI + M_PI / 4.0);
    assert(r >= 0.0 && r <= 1.0);
  }

  return 0;
}
