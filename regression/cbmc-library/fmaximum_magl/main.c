#include <assert.h>
#include <math.h>

// C23; declared here as not all C libraries declare it yet
long double fmaximum_magl(long double, long double);

int main()
{
  assert(!signbit(fmaximum_magl(0.0, -0.0)));
  assert(!signbit(fmaximum_magl(-0.0, 0.0)));

  long double x, y;
  long double r = fmaximum_magl(x, y);

  if(isnan(x) || isnan(y))
  {
    assert(isnan(r));
    return 0;
  }

  assert(r == x || r == y);
  assert(fabsl(r) >= fabsl(x));
  assert(fabsl(r) >= fabsl(y));
  if(fabsl(x) == fabsl(y))
  {
    assert(r >= x && r >= y);
    if(x == 0)
      assert(signbit(r) == (signbit(x) && signbit(y)));
  }

  return 0;
}
