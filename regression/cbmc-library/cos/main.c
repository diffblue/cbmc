#define _USE_MATH_DEFINES
#include <assert.h>
#include <math.h>

int main()
{
  // cos(0) = 1 exactly
  double c = cos(0.0);
  assert(c == 1.0);

  // cos(π/2) is in [0, 1] (first quadrant boundary)
  c = cos(M_PI / 2.0);
  assert(c >= 0.0 && c <= 1.0);

  // cos(π) is in [-1, 0]
  c = cos(M_PI);
  assert(c >= -1.0 && c <= 0.0);

  // cos(-π) is in [-1, 0]
  c = cos(-M_PI);
  assert(c >= -1.0 && c <= 0.0);

  // cos(2π) is in [0, 1]
  c = cos(2.0 * M_PI);
  assert(c >= 0.0 && c <= 1.0);

  // Range narrowing: cos(x) >= 0 for x in [-π/2, π/2]
  {
    double x;
    __CPROVER_assume(x >= -M_PI / 2.0 + 0.1 && x <= M_PI / 2.0 - 0.1);
    double r = cos(x);
    assert(r >= 0.0 && r <= 1.0);
  }

  // Range narrowing: cos(x) <= 0 for x in [π/2, 3π/2]
  {
    double x;
    __CPROVER_assume(x >= M_PI / 2.0 + 0.1 && x <= 3.0 * M_PI / 2.0 - 0.1);
    double r = cos(x);
    assert(r >= -1.0 && r <= 0.0);
  }

  // Range reduction: cos at large input (4π reduces to [0,1] quadrant)
  {
    double r = cos(4.0 * M_PI + M_PI / 4.0);
    assert(r >= 0.0 && r <= 1.0);
  }

  return 0;
}
