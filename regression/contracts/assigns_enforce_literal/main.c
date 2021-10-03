#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int foo(int *x) __CPROVER_assigns(12)
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
