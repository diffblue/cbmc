#include <assert.h>

void foo(int *x, int *y) __CPROVER_assigns(*x)
{
  *x = 7;
}

int main()
{
  int n;
  int m = 4;
  bar(&n);
  assert(m == 4);

  return 0;
}
