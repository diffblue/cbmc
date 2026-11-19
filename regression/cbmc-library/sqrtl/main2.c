#include <assert.h>
#include <fenv.h>
#include <math.h>

int main(void)
{
  // 1 + the distance to the next long double, computed in the target's
  // long double format (which the host's LDBL_EPSILON need not match)
  long double eps = 1.0L;
  while(1.0L + eps / 2 != 1.0L)
    eps /= 2;
  long double x = 1.0L + eps;
  assert(x != 1.0L);
  // the exact root is just below 1 + eps / 2, the midpoint between 1 and the
  // next long double
  assert(sqrtl(x) == 1.0L);
  fesetround(FE_UPWARD);
  assert(sqrtl(x) == x);
  return 0;
}
