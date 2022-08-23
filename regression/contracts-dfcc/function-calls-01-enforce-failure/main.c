#include <assert.h>
int f(int *x)
  // clang-format off
__CPROVER_requires(0 <= *x && *x <= 10000)
__CPROVER_ensures(__CPROVER_return_value == *x + 1)
__CPROVER_ensures(1 <= __CPROVER_return_value && __CPROVER_return_value <= 10001)
// clang-format on
{
  if(*x >= 10000)
    return 0; // reachable under preconditions
  return *x + 1;
}

int main()
{
  int x;
  f(&x);
  return 0;
}
