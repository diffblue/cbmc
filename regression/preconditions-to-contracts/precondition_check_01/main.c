// This tests whether preconditions are correctly turned to contracts
// by checking whether the contract holds

#include <assert.h>

int min(int a, int b) __CPROVER_ensures(
  __CPROVER_return_value <= a && __CPROVER_return_value <= b &&
  (__CPROVER_return_value == a || __CPROVER_return_value == b))
{
  __CPROVER_precondition(a >= 0, "");
  __CPROVER_precondition(b >= 0, "");
  if(a <= b)
  {
    return a;
  }
  else
  {
    return b;
  }
}

int main()
{
  int x, y, z;
  __CPROVER_assume(x >= 0 && y >= 0);
  z = min(x, y);
  assert(z <= x);
}
