#include <assert.h>
#include <limits.h>

void foo(int *x) __CPROVER_assigns(*x) __CPROVER_requires(*x > 0)
  __CPROVER_ensures(*x == __CPROVER_old(*x) + 2)
{
  *x = *x + 2;
}

int main()
{
  int n;
  __CPROVER_assume(n > 0 && n < INT_MAX - 2);
  foo(&n);

  assert(n > 2);

  return 0;
}
