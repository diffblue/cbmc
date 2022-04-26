#include <assert.h>
#include <stddef.h>

int *z;

void bar(int *x, int *y)
{
  *x = 3;
  if(y != NULL)
    *y = 5;
}

void baz(int c)
{
  // does a side effect on a global, but
  // in the calling context of foo the branch is dead
  if(c)
    *z = 7;
}

void foo(int *x) __CPROVER_assigns(*x) __CPROVER_requires(*x > 0)
  __CPROVER_ensures(*x == 3)
{
  bar(x, NULL);
  *x = 3;
  baz(0);
}

int main()
{
  int n;
  foo(&n);
  assert(n == 3);
  return 0;
}
