#include <assert.h>

double nondet_double();

int main(void)
{
  double d = nondet_double();

  __CPROVER_assume(d < 0x1.0p+63 && d > 0x1.0p+53);

  long long int i = d;
  double d1 = i;

  assert(d1 != 0x0);

  return 0;
}

