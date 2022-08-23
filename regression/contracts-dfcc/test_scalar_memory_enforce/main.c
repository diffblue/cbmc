#include <assert.h>
#include <stdbool.h>

bool ptr_ok(int *x)
{
  return (*x < 5);
}

bool return_ok(int ret_value, int *x)
{
  int a = *x;
  return (ret_value == (*x + 5));
}

// clang-format off
int foo(int *x)
  __CPROVER_assigns(*x)
  __CPROVER_requires(
    __CPROVER_is_fresh(x, sizeof(int)) &&
    *x > 0 &&
    ptr_ok(x))
  __CPROVER_ensures(
    !ptr_ok(x) &&
    !__CPROVER_is_fresh(x, sizeof(int)) &&
    return_ok(__CPROVER_return_value, x))
// clang-format on
{
  *x = *x + 4;
  return (*x + 5);
}

int main()
{
  int *n;
  int o = foo(n);
  return 0;
}
