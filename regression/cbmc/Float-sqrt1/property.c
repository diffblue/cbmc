#include <assert.h>
#include <math.h>

double nondet_double(void);

int main(void)
{
  // a property for all arguments of at least 1
  double y = nondet_double();
  __CPROVER_assume(y >= 1);
  assert(sqrt(y) <= y);
  return 0;
}
