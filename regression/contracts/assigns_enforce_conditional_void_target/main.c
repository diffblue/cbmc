#include <stdbool.h>

int foo(bool a, void *x) __CPROVER_assigns(a : *x)
{
  return 0;
}

int main()
{
  bool a;
  int x;

  foo(a, &x);
  return 0;
}
