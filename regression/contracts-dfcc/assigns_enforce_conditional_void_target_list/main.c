#include <stdbool.h>

int foo(bool a, void *x, int *y) __CPROVER_assigns(a : *x, *y)
{
  return 0;
}

int main()
{
  bool a;
  int x;

  foo(a, &x, &x);

  return 0;
}
