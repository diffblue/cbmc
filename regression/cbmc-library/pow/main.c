#include <assert.h>
#include <float.h>
#include <math.h>

int main()
{
  double four = pow(2.0, 2.0);
  assert(four > 3.999 && four < 4.345);

  double x;
  __CPROVER_assume(isnormal(x));
  double limit = 1 << 15;
  __CPROVER_assume(x > -limit && x < limit);
  __CPROVER_assume(x > FLT_MIN || x < -FLT_MIN);
  double sq = pow(x, 2.0);
  assert(sq >= 0.0);

  return 0;
}
