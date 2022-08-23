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
  if(0 <= x && x <= 10001)
  {
    // f gets called outside of its preconditions we expect checks to fail
    int __return_value = f(&x);
    // we expect this to hold regardless after contract replacement
    // because post conditions are assumed regardless of the contract's
    // precondition status
    assert(__return_value == x + 1);
    assert(1 <= __return_value && __return_value <= 10001);
  }
  return 0;
}
