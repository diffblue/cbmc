#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int z;

// clang-format off
int foo(int *x, int *y)
  __CPROVER_assigns(z, *x)
  __CPROVER_requires(
    __CPROVER_is_fresh(x, sizeof(int)) &&
    *x > 0 &&
    *x < 4)
  __CPROVER_ensures(
    x != NULL &&
    !__CPROVER_is_fresh(x, sizeof(int)) &&
    __CPROVER_is_fresh(y, sizeof(int)) &&
    x != y &&
    __CPROVER_return_value == *x + 5)
// clang-format on
{
  *x = *x + 4;
  y = malloc(sizeof(*y));
  *y = *x;
  z = *y;
  return (*x + 5);
}

int main()
{
  int n = 4;
  n = foo(&n, &n);
  assert(!(n < 4));
  return 0;
}
