#include <assert.h>
#include <fenv.h>
#include <math.h>

int main(void)
{
  // subnormal arguments have a single correctly rounded (normal) root
  double x = 0x1p-1073;
  assert(sqrt(x) == 0x1.6a09e667f3bcdp-537);
  fesetround(FE_DOWNWARD);
  assert(sqrt(x) == 0x1.6a09e667f3bccp-537);
  return 0;
}
