#include <assert.h>
#include <stdlib.h>

int x = 0;

void quz() __CPROVER_assigns(x) __CPROVER_ensures(x == -1)
{
  x = -1;
}

int baz() __CPROVER_assigns()
{
  return 5;
}

void bar(int *y, int w) __CPROVER_assigns(*y)
{
  *y = 3;
  w = baz();
  assert(w == 5);
  quz();
}

void foo(int *y, int z) __CPROVER_assigns(*y)
{
  int w = 5;
  assert(w == 5);
  bar(y, w);
  z = -2;
}

int main()
{
  int *y = malloc(sizeof(*y));
  *y = 0;
  int z = 1;
  foo(y, z);
  assert(x == -1);
  assert(*y == 3);
  assert(z == 1);
  return 0;
}
