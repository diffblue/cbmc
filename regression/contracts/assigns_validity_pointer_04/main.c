#include <assert.h>
#include <stddef.h>

int *z;

void bar(int *x, int *y) __CPROVER_assigns(*x, *y) __CPROVER_requires(*x > 0)
  __CPROVER_ensures(*x == 3 && *y == 5)
{
}

void baz() __CPROVER_assigns(*z) __CPROVER_ensures(*z == 7)
{
}

void foo(int *x) __CPROVER_assigns(*x) __CPROVER_requires(*x > 0)
  __CPROVER_ensures(*x == 3)
{
  int *y = malloc(sizeof(int));
  bar(x, y);
  assert(*y == 5);

  z = malloc(sizeof(int));
  baz();
  assert(*z == 7);
}

int main()
{
  int n;
  foo(&n);

  assert(n == 3);
  return 0;
}
