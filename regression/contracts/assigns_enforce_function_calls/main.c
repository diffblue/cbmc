#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int *bar(int *x)
{
  return *x;
}

int foo(int *x) __CPROVER_assigns(bar(x))
{
  *x = 0;
  return 0;
}

int main()
{
  int x;
  foo(&x);
  return 0;
}
