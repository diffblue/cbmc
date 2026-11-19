#include <assert.h>
#include <math.h>

// C23; declared here as not all C libraries declare it yet
float fminimumf(float, float);

int main()
{
  assert(signbit(fminimumf(0.0, -0.0)));
  assert(signbit(fminimumf(-0.0, 0.0)));

  float x, y;
  float r = fminimumf(x, y);

  if(isnan(x) || isnan(y))
  {
    assert(isnan(r));
    return 0;
  }

  assert(r == x || r == y);
  assert(r <= x && r <= y);
  if(x == 0 && y == 0)
    assert(signbit(r) == (signbit(x) || signbit(y)));

  return 0;
}
