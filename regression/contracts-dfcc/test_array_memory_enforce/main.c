#include <stdbool.h>

bool ptr_ok(int *x)
{
  return (0 < *x && *x < 5);
}

bool return_ok(int ret_value, int *x)
{
  return (ret_value == *x + 5);
}

int foo(int *x)
  // clang-format off
__CPROVER_assigns(__CPROVER_object_from(x))
__CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int) * 10) &&  ptr_ok(x))
__CPROVER_ensures(
    !ptr_ok(x) &&
    x[9] == 113 &&
    return_ok(__CPROVER_return_value, x))
// clang-format on
{
  *x = *x + 4;
  x[5] = 12;
  x[9] = 113;
  return *x + 5;
}

int main()
{
  int *n;
  int o = foo(n);
  return 0;
}
