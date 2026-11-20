#include <assert.h>
#include <math.h>

int main(void)
{
  // Compute the operands at run time, as --dump-c prints floating-point
  // constants with limited precision.
  int p = 1 << 23;
  float e = 1.0f / p;
  float x = 1.0f + e;
  // (1 + 2^-23)^2 = 1 + 2^-22 + 2^-46: the product must not be rounded
  float r = fmaf(x, x, -(1.0f + 2 * e));
  assert(r == e * e);

  long long q = 1LL << 60;
  long double y = 1.0L + 1.0L / q;
  // 1 + 2^-60 is not representable in double precision
  long double s = fmal(y, 1.0L, 0.0L);
  assert(s == y);

  return 0;
}
