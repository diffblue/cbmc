#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int foo(bool a, int *x, long long *y) __CPROVER_assigns(*(a ? x : y++))
{
  if(a)
  {
    *x = 0;
  }
  else
  {
    *y = 0;
  }
  return 0;
}

int main()
{
  bool a;
  int x;
  long y;

  foo(true, &x, &y);
  return 0;
}
