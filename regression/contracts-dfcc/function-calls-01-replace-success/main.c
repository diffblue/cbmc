#include <assert.h>
int f(int *x)
  // clang-format off
__CPROVER_requires(0 <= *x && *x <= 10000)
__CPROVER_ensures(__CPROVER_return_value == *x + 1)
__CPROVER_ensures(1 <= __CPROVER_return_value && __CPROVER_return_value <= 10001)
// clang-format on
{
  return *x + 1;
}

int main()
{
  int x;
  if(0 <= x && x <= 10000)
  {
    int __return_value = f(&x);
    assert(__return_value == x + 1);
    assert(1 <= __return_value && __return_value <= 10001);
  }
  return 0;
}
