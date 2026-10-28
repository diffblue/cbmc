#include <assert.h>
#include <fenv.h>
#include <math.h>

int main(void)
{
  long double eps = 1.0L;
  while(1.0L + eps / 2 != 1.0L)
    eps /= 2;
  // binary128: an exact square of a subnormal argument
  if(eps == 0x1p-112L)
    assert(sqrtl(0x1p-16492L) == 0x1p-8246L);

  // exact squares are returned as they are when rounding upward, and the
  // caller's rounding mode is preserved
  fesetround(FE_UPWARD);
  assert(sqrtf(4.0f) == 2.0f);
  assert(sqrt(4.0) == 2.0);
  assert(sqrtl(4.0L) == 2.0L);
  assert(fegetround() == FE_UPWARD);
  return 0;
}
