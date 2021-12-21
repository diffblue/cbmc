#include <stdbool.h>
#include <stdlib.h>

int bar(int l, int r) __CPROVER_requires(0 <= l && l <= 10)
  __CPROVER_requires(0 <= r && r <= 10) __CPROVER_assigns() __CPROVER_ensures(
    __CPROVER_return_value == __CPROVER_old(l) + __CPROVER_old(r))
{
  return l + r;
}

int *baz(int l, int r) __CPROVER_requires(0 <= l && l <= 10)
  __CPROVER_requires(0 <= r && r <= 10) __CPROVER_assigns() __CPROVER_ensures(
    *__CPROVER_return_value == __CPROVER_old(l) + __CPROVER_old(r))
{
  int *res = malloc(sizeof(int));
  *res = l + r;
  return res;
}

int foo(int l, int r) __CPROVER_requires(0 <= l && l <= 10)
  __CPROVER_requires(0 <= r && r <= 10) __CPROVER_assigns() __CPROVER_ensures(
    __CPROVER_return_value == __CPROVER_old(l) + __CPROVER_old(r))
{
  bar(l, r);
  bar(l, r);
  baz(l, r);
  baz(l, r);
  return l + r;
}

int main()
{
  int l;
  int r;
  foo(l, r);
  return 0;
}
