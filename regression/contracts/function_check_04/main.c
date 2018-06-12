// function_check_04

// Note that this test is supposed to have an incorrect contract.
// We verify that checking this faulty contract (correctly) yields a failure.

#include <assert.h>

int foo() 
  __CPROVER_ensures(__CPROVER_return_value == 0)
{
  return 1;
}

int main()
{
  int x = foo();
  assert(x == 0);
  return 0;
}
