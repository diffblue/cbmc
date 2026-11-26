#include <assert.h>

int foo(int x)
  // clang-format off
__CPROVER_requires(0 <= x && x < 1000)
__CPROVER_ensures(__CPROVER_return_value == x + 1)
// clang-format on
{
  return x + 1;
}

int main()
{
  // First top-level call: checked against the contract.
  int a = foo(1);
  assert(a == 2);
  // Sequential top-level re-invocation: summarised by contract replacement.
  int b = foo(a);
  assert(b == 3);
  return 0;
}
