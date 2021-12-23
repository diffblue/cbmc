#include <stdbool.h>

bool cond()
{
  return true;
}

int foo(int a, int *x, int *y)
  // clang-format off
__CPROVER_assigns(a && cond() : *x)
// clang-format on
{
  if(a)
  {
    if(cond())
      *x = 0; // must pass
  }
  else
  {
    *x = 0; // must fail
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
