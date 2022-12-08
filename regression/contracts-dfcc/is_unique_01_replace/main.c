#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

bool ptr_ok(int *x)
{
  return 0 < *x && *x < 5;
}

bool return_ok(int ret_value, int *x)
{
  return ret_value == (*x + 5);
}

int foo(int *x)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)))
__CPROVER_requires(ptr_ok(x))
__CPROVER_assigns(*x)
__CPROVER_ensures(!ptr_ok(x))
__CPROVER_ensures(return_ok(__CPROVER_return_value, x))
// clang-format on
{
  *x = *x + 4;
  return *x + 5;
}

void main()
{
  int x;
  int *_x = &x;
  if(ptr_ok(_x))
  {
    int ret_val = foo(_x);
    assert(!ptr_ok(_x));
    assert(return_ok(ret_val, _x));
  }
}
