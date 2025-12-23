#include <assert.h>
#include <math.h>

int main()
{
  long double d1, d2;
  __CPROVER_assume(!isnan(d1) || !isnan(d2));
  long double r = fminl(d1, d2);
  assert(!isnan(d1) || r == d2);
  assert(!isnan(d2) || r == d1);
  assert(isnan(d1) || isnan(d2) || (d1 < d2 ? r == d1 : r == d2));
  return 0;
}
