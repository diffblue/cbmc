#include <assert.h>

void foo(int *x) __CPROVER_assigns(*x) __CPROVER_requires(*x == 0)
  __CPROVER_ensures(*x >= __CPROVER_old(*x) + 2)
{
  *x = *x + 2;
}

int main()
{
  int n = 0;
  foo(&n);

  assert(n >= 2);

  return 0;
}
