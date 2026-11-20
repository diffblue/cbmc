#include <assert.h>
#include <math.h>

// C23; declared here as not all C libraries declare it yet
double fmaximum_num(double, double);

int main()
{
  assert(!signbit(fmaximum_num(0.0, -0.0)));
  assert(!signbit(fmaximum_num(-0.0, 0.0)));

  double x, y;
  double r = fmaximum_num(x, y);

  if(isnan(x) && isnan(y))
  {
    assert(isnan(r));
    return 0;
  }
  if(isnan(x) || isnan(y))
  {
    // the other, numeric argument is returned unchanged
    double other = isnan(x) ? y : x;
    assert(r == other && signbit(r) == signbit(other));
    return 0;
  }

  assert(r == x || r == y);
  assert(r >= x && r >= y);
  if(x == 0 && y == 0)
    assert(signbit(r) == (signbit(x) && signbit(y)));

  return 0;
}
