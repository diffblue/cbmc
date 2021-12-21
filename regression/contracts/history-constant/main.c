#include <stdio.h>

int foo(int l) __CPROVER_requires(-10 <= l && l <= 10) __CPROVER_ensures(
  __CPROVER_return_value == __CPROVER_old(l) + __CPROVER_old(10))
{
  return l + 10;
}

int main()
{
  int l;
  __CPROVER_assume(-10 <= l && l <= 10);
  foo(l);
  return 0;
}
