#include <assert.h>
#include <fenv.h>
#include <float.h>
#include <math.h>

int main(void)
{
  // IEEE 754 squareRoot is correctly rounded (C11 F.10.4.5)
  double x = 1.0 + DBL_EPSILON;
  // the exact root is 1.000000000000000111..., below the midpoint between
  // 1.0 and the next double
  assert(sqrt(x) == 1.0);

  double y = 2.0;
  fesetround(FE_DOWNWARD);
  assert(sqrt(y) == 0x1.6a09e667f3bccp+0);
  fesetround(FE_TOWARDZERO);
  assert(sqrt(y) == 0x1.6a09e667f3bccp+0);
  fesetround(FE_UPWARD);
  assert(sqrt(y) == 0x1.6a09e667f3bcdp+0);

  return 0;
}
