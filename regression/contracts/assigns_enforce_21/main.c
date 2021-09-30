#include <assert.h>
#include <stdlib.h>

int x = 0;

void foo(void *y) __CPROVER_assigns(*y) __CPROVER_assigns(x)
{
  x = 2;
  int *bar = (int *)y;
  *bar = 2;
}

int main()
{
  int *y = malloc(sizeof(*y));
  *y = 0;
  foo(y);
  assert(x == 2);
  assert(*y == 2);
  return 0;
}
