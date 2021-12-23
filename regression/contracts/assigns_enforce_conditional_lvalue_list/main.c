#include <stdbool.h>

int foo(bool a, int *x, int *y) __CPROVER_assigns(a : *x, *y)
{
  if(a)
  {
    *x = 0; // must pass
    *y = 0; // must pass
  }
  else
  {
    *x = 0; // must fail
    *y = 0; // must fail
  }

  *x = 0; // must fail
  *y = 0; // must fail
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
