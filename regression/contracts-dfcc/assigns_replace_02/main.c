#include <assert.h>

void foo(int *x) __CPROVER_assigns(*x)
{
  *x = 7;
}

int main()
{
  int n;
  int m = 4;
  foo(&n);
  assert(m == 4);

  return 0;
}
