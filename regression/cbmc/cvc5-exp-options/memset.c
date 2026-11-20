#include <assert.h>
#include <string.h>

unsigned nondet_unsigned(void);

int main(void)
{
  int a[4];
  memset(a, 0, sizeof a);
  unsigned i = nondet_unsigned();
  __CPROVER_assume(i < 4);
  assert(a[i] == 0);
  return 0;
}
