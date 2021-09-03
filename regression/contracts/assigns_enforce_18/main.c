#include <assert.h>
#include <stdlib.h>

int x = 0;
int y = 0;

void foo(int *xp, int *xq, int a) __CPROVER_assigns(*xp)
{
  a = 2;
  int *yp = malloc(sizeof(int));
  free(yp);
  int z = 3;
  *xp = 1;
  y = -1;
}

void bar(int *a, int *b) __CPROVER_assigns(a, *b)
{
  free(a);
  *b = 0;
}

int main()
{
  int z = 0;
  foo(&x, &z, z);
  assert(x == 1);
  assert(y == -1);
  assert(z == 0);
  int *a = malloc(sizeof(*a));
  int b = 1;
  bar(a, &b);
  assert(b == 0);
  return 0;
}
