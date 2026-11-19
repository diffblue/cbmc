#include <assert.h>
#include <math.h>

// C23; declared here as not all C libraries declare it yet
float fminimum_magf(float, float);

int main()
{
  assert(signbit(fminimum_magf(0.0, -0.0)));
  assert(signbit(fminimum_magf(-0.0, 0.0)));

  float x, y;
  float r = fminimum_magf(x, y);

  if(isnan(x) || isnan(y))
  {
    assert(isnan(r));
    return 0;
  }

  assert(r == x || r == y);
  assert(fabsf(r) <= fabsf(x));
  assert(fabsf(r) <= fabsf(y));
  if(fabsf(x) == fabsf(y))
  {
    assert(r <= x && r <= y);
    if(x == 0)
      assert(signbit(r) == (signbit(x) || signbit(y)));
  }

  return 0;
}
