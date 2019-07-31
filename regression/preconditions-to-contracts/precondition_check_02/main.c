// Note that this test is supposed to have a false precondition, and
// we check whether CBMC can detect this failure

#include <assert.h>

int foo(int x) __CPROVER_ensures(__CPROVER_return_value == 1)
{
  __CPROVER_precondition(x == 0, "");
  return 1;
}

int main()
{
  int in;
  int x = foo(in);
  assert(x == 1);
  return 0;
}
