#include <assert.h>
#include <stdlib.h>

static int add_operator(int *x, int *y)
{
  int old_y = *y;
  *y = 0;              // BUG
  return (*x + old_y); // mask the error
}

// clang-format off
int foo(int *x, int *y)
  __CPROVER_requires(x != NULL)
  __CPROVER_requires(y != NULL)
  __CPROVER_ensures(
    __CPROVER_return_value == (__CPROVER_old(*x) + __CPROVER_old(*y)))
// clang-format on
{
  int (*sum)(int *, int *) = add_operator;
  return sum(x, y);
}

int main()
{
  int x;
  int y;
  foo(&x, &y);
  return 0;
}
