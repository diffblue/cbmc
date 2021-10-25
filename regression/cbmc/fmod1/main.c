#include <assert.h>
#include <math.h>

void main()
{
  // If x is +-0 and y is not zero, +-0 is returned
  assert(fmod(0.0, 1.0) == 0.0);
  assert(fmod(-0.0, 1.0) == -0.0);

  // If x is +-oo and y is not NaN, NaN is returned and FE_INVALID is raised
  assert(isnan(fmod(INFINITY, 1.0)));
  assert(isnan(fmod(-INFINITY, 1.0)));

  // If y is +-0 and x is not NaN, NaN is returned and FE_INVALID is raised
  assert(isnan(fmod(1.0, 0.0)));
  assert(isnan(fmod(1.0, -0.0)));

  // If y is +-oo and x is finite, x is returned.
  assert(fmod(1.0, INFINITY) == 1.0);
  assert(fmod(1.0, -INFINITY) == 1.0);

  // If either argument is NaN, NaN is returned
  assert(isnan(fmod(1.0, NAN)));
  assert(isnan(fmod(NAN, 1.0)));
}
