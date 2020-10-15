#include <assert.h>

void foo(int *x) __CPROVER_assigns(*x)
{
  *x = 7;
}

int main()
{
  int n = 6;
  foo(&n);
  assert(n == 7);
  assert(n == 6);
  return 0;
}
