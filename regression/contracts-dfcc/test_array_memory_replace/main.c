#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

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
  int *x = malloc(sizeof(int) * 10);
  if(ptr_ok(x))
  {
    int o = foo(x);
    assert(!ptr_ok(x));
    assert(x[9] == 113);
    assert(return_ok(o, x));
  }
  return 0;
}
