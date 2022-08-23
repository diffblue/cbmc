#include <stdbool.h>

int *identity(int *ptr)
{
  return ptr;
}

int foo(bool a, int *x, int offset) __CPROVER_assigns(a : !x)
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
