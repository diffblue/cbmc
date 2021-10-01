#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int foo(bool a, int *x, int *y, int *z) __CPROVER_assigns(*(a ? x : y))
{
  if(a)
  {
    *x = 0; // must pass
  }
  else
  {
    // must pass because in the context of main, this branch is dead
    // so foo never attempts to write to *z.
    *z = 0;
  }
  return 0;
}

int main()
{
  bool a;
  int x;
  int y;
  int z;

  foo(true, &x, &y, &z);
  return 0;
}
