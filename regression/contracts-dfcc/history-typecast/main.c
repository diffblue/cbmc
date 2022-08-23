#include <stdio.h>

long bar(long l, long r) __CPROVER_requires(-10 <= l && l <= 10)
  __CPROVER_requires(-10 <= r && r <= 10) __CPROVER_ensures(
    __CPROVER_return_value == __CPROVER_old(l) + __CPROVER_old(r))
{
  return l + r;
}

int foo(int l, int r) __CPROVER_requires(-10 <= l && l <= 10)
  __CPROVER_requires(-10 <= r && r <= 10) __CPROVER_ensures(
    __CPROVER_return_value == __CPROVER_old(l) + __CPROVER_old(r))
{
  return bar((long)l, (long)r);
}

int main()
{
  int n;
  __CPROVER_assume(-10 <= n && n <= 10);
  foo(n, n);
  return 0;
}
