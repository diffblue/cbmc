#include <assert.h>
#include <math.h>

int main()
{
  float f1, f2;
  __CPROVER_assume(!isnan(f1) || !isnan(f2));
  float r = fminf(f1, f2);
  assert(!isnan(f1) || r == f2);
  assert(!isnan(f2) || r == f1);
  assert(isnan(f1) || isnan(f2) || (f1 < f2 ? r == f1 : r == f2));
  return 0;
}
