#include <assert.h>

void foo(int *x) __CPROVER_assigns(*x) __CPROVER_requires(*x == 0)
  __CPROVER_ensures(*x >= __CPROVER_old(*x))
{
  *x = *x + 1;
}

int main()
{
  int x = 0;
  int old_x = x;
  foo(&x);
  assert(x >= old_x);
  return 0;
}
