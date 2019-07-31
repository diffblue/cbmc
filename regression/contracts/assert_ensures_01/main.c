// This tests whether the flag --assert-ensures adds the assert of the
// ensures statement after the call

#include <assert.h>

int min(int a, int b) __CPROVER_ensures(
  __CPROVER_return_value <= a && __CPROVER_return_value <= b &&
  (__CPROVER_return_value == a || __CPROVER_return_value == b))
{
  return 100;
}

int main()
{
  int x, y, z;
  z = min(x, y);
  return z;
}
