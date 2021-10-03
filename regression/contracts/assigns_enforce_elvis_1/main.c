#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int foo(bool a, int *x, int *y, int *z) __CPROVER_assigns(*(a ? x : y))
{
  if(a)
    *x = 0; // must pass
  else
    *y = 0; // must pass
  return 0;
}

int main()
{
  bool a;
  int x;
  int y;
  int z;

  foo(a, &x, &y, &z);
  return 0;
}
