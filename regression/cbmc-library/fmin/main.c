#include <assert.h>
#include <math.h>

int main()
{
  double d1, d2;
  __CPROVER_assume(!isnan(d1) || !isnan(d2));
  double r = fmin(d1, d2);
  assert(!isnan(d1) || r == d2);
  assert(!isnan(d2) || r == d1);
  assert(isnan(d1) || isnan(d2) || (d1 < d2 ? r == d1 : r == d2));
  return 0;
}
