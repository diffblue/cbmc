#include <assert.h>
#include <stdlib.h>

void baz(int *x, int y)
{
  *x = y;
  return;
}

void bar(int *x, int y)
{
  baz(x, y);
  return;
}

void foo(int *x, int *y, int *z) __CPROVER_assigns(*x)
{
  // this write is allowed
  baz(x, 1);
  __CPROVER_assert(*x == 1, "foo.x.set");

  // this write is allowed
  int local;
  bar(&local, 2);
  __CPROVER_assert(local == 2, "foo.local.set");

  // this write is not allowed
  baz(y, 3);
  __CPROVER_assert(*y == 3, "foo.y.set");

  // this write is not allowed
  bar(z, 4);
  __CPROVER_assert(*z == 4, "foo.z.set");

  return;
}

int main()
{
  int x;
  int y;
  int z;
  foo(&x, &y, &z);
  return 0;
}
