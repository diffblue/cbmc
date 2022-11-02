#include <assert.h>
#include <stddef.h>

int *z;

void bar(int *x, int *y) __CPROVER_assigns(*x, *y) __CPROVER_requires(*x > 0)
  __CPROVER_ensures(*x == 3 && (y == NULL || *y == 5))
{
  *x = 3;
  if(y != NULL)
    *y = 5;
}

void baz() __CPROVER_assigns(*z) __CPROVER_ensures(z == NULL || *z == 7)
{
  if(z != NULL)
    *z = 7;
}

void foo(int *x) __CPROVER_assigns(*x, *z) __CPROVER_requires(*x > 0)
  __CPROVER_ensures(*x == 3)
{
  bar(x, NULL);
  baz();
}

int main()
{
  int n;
  z = malloc(sizeof(*z));
  foo(&n);

  assert(n == 3);
  assert(z == NULL || *z == 7);
  return 0;
}
