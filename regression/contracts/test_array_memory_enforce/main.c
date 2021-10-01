#include <stdbool.h>

bool ptr_ok(int *x)
{
  return (*x < 5);
}

bool return_ok(int ret_value, int *x)
{
  int a;
  a = *x;
  return (ret_value == *x + 5);
}

// clang-format off
int foo(int *x)
  __CPROVER_assigns(__CPROVER_POINTER_OBJECT(x))
  __CPROVER_requires(
    __CPROVER_is_fresh(x, sizeof(int) * 10) &&
    x[0] > 0 &&
    ptr_ok(x))
  __CPROVER_ensures(
    !ptr_ok(x) &&
    !__CPROVER_is_fresh(x, sizeof(int) * 10) && /* `x` is not fresh anymore. */
    x[9] == 113 &&
    return_ok(__CPROVER_return_value, x))
// clang-format on
{
  *x = *x + 4;
  x[5] = 12;
  x[9] = 113;
  int y = *x + 5;
  return *x + 5;
}

int main()
{
  int *n;
  int o = foo(n);
  return 0;
}
