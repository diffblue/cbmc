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

void foo(int *x) __CPROVER_assigns()
{
  // not allowed, failed check in baz
  bar(x, 2);
}

int main()
{
  int x;
  foo(&x);
  return 0;
}
