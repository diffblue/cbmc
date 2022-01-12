#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int foo(int *x) __CPROVER_assigns(*(x + 10))
{
  // should fail in the context of main because the allocated object is too small
  *(x + 10) = 0;
  return 0;
}

int main()
{
  int *x = malloc(2 * sizeof(int));
  *x = 0;
  *(x + 1) == 0;
  // write should fail because x points to a size 2 object and the contracts expects size 10 at least.
  foo(x);
  return 0;
}
