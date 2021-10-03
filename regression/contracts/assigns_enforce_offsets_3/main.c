#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int foo(int *x) __CPROVER_assigns(*(x + 1))
{
  // should pass
  *(x + 1) = 0;
  return 0;
}

int main()
{
  int *x = malloc(2 * sizeof(int));
  *x = 0;
  *(x + 1) = 12;
  foo(x);
  assert(*(x + 1) == 0);
  return 0;
}
