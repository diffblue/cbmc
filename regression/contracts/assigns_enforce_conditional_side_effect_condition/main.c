#include <stdbool.h>

int foo(int a, int *x, int *y) __CPROVER_assigns(a++ : *x)
{
  if(a)
  {
    *x = 0;
  }
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
