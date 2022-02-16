#include <assert.h>
#include <stdlib.h>

int x = 0;

void foo(int *y) __CPROVER_assigns()
{
  __CPROVER_havoc_object(y);
  x = 2;
}

int main()
{
  int *y = malloc(sizeof(*y));
  *y = 0;
  foo(y);
  assert(x == 2);
  return 0;
}
