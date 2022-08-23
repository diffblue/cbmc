#include <assert.h>
#include <stdlib.h>

int foo(int *x) __CPROVER_requires(x != NULL)
{
  return *x + 5;
}

int main()
{
  int n = 10;
  assert(foo(&n) != 15);
  return 0;
}
