#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

// When enforced, this contract should pass

// clang-format off
bool sub_ptr_values(int *x, int *y)
  __CPROVER_requires(
    __CPROVER_is_fresh(x, sizeof(int)) &&
    (y == x || __CPROVER_is_fresh(y, sizeof(int)))
  )
  __CPROVER_ensures(
    __CPROVER_return_value == (*x - *y)
  )
// clang-format on
{
  return (*x - *y);
}

// A function that uses `sub_ptr_values`
void main()
{
  int *n = malloc(sizeof(int));
  int diff = sub_ptr_values(n, n);
}
