#include <assert.h>
#include <limits.h>

void foo(int *x) __CPROVER_assigns(*x)
  __CPROVER_requires(0 <= *x && *x < INT_MAX)
    __CPROVER_ensures(*x == __CPROVER_old(*x) + 1)
{
  *x = *x + 1;
}

int main()
{
  int x;
  __CPROVER_assume(0 <= x && x < INT_MAX);
  int old_x = x;
  foo(&x);
  assert(x == old_x + 1);
  return 0;
}
