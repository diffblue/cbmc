// function_apply_01

// Note that this test is supposed to have an incorrect contract.
// We verify that applying (without checking) the contract yields success,
// and that checking the contract yields failure.

#include <assert.h>

int foo() __CPROVER_ensures(__CPROVER_return_value == 0)
{
  return 1;
}

int main()
{
  int x = foo();
  assert(x == 0);
  return 0;
}
