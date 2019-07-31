// This tests whether --assert-ensures correctly handles function
// calls in the contract

#include <assert.h>

int is_min(int min, int a, int b)
{
  return min <= a && min <= b && (min == a || min == b);
}

int min(int a, int b) __CPROVER_ensures(is_min(__CPROVER_return_value, a, b))
{
  return 100;
}

int main()
{
  int x, y, z;
  z = min(x, y);
  return z;
}
