#include <assert.h>

long double nondet_ld(void);

int main(void)
{
  long double x = nondet_ld();
  __CPROVER_assume(x == 1.0L);
  assert(x + x == 2.0L);
  return 0;
}
