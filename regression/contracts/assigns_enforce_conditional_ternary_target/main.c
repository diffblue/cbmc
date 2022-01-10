#include <stdbool.h>

int foo(bool a, int *x, int *y) __CPROVER_assigns(a : (x ? *x : *y))
{
  return 0;
}

int main()
{
  bool a;
  int x;
  int y;

  foo(a, &x, &y);
  return 0;
}
