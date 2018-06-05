// function_check_05

// This test checks that when a function call is replaced by an invariant,
// it adequately havocs the locations modified by the function.
// This test currently fails because the analysis of what is modified by
// a function is flawed.

#include <assert.h>

int foo(int *x) 
  __CPROVER_ensures(__CPROVER_return_value == 1)
{
  *x = 1;
  return 1;
}

int main()
{
  int y = 0;  
  int z = foo(&y);
  // This assert should fail.
  assert(y == 0);
  // This one should succeed.
  assert(z == 1);
  return 0;
}
