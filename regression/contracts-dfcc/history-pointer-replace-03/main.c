#include <assert.h>

void foo(int *x) __CPROVER_assigns(*x)
  __CPROVER_requires(*x == __CPROVER_old(*x))
    __CPROVER_ensures(*x == __CPROVER_old(*x) + 1)
{
  *x = *x + 1;
}

int main()
{
  int x;
  int old_x = x;
  foo(&x);
  assert(x == old_x + 1);
  return 0;
}
