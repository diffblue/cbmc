// function_check_01

// This tests a simple example of a function with requires and
// ensures which should both be satisfied.

#include <assert.h>

int min(int a, int b)
  __CPROVER_requires(a >= 0 && b >= 0)
  __CPROVER_ensures(__CPROVER_return_value <= a &&
                    __CPROVER_return_value <= b &&
                   (__CPROVER_return_value == a || __CPROVER_return_value == b)
                   )
{
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
