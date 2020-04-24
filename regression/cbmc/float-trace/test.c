#include <assert.h>
#include <math.h>
#include <stdbool.h>

int main()
{
  float zero = 0.0f;
  float one = 1.0f;
  float complex = 0x1p+37f;
  float inf = INFINITY;
  float nan = NAN;

  double dzero = 0.0;
  double done = 1.0;
  double dinf = INFINITY;
  double dnan = NAN;
  double dcomplex = -5.56268e-309;

  assert(false);

  return 0;
}

void test(float value)
{
  assert(value == 1.0f);
  assert(value == 0.0f);
}
