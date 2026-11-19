#include <assert.h>
#include <fenv.h>
#include <math.h>

int main(void)
{
  // subnormal arguments have a single correctly rounded (normal) root
  float x = 0x1p-149f;
  assert(sqrtf(x) == 0x1.6a09e6p-75f);
  fesetround(FE_UPWARD);
  assert(sqrtf(x) == 0x1.6a09e8p-75f);
  return 0;
}
