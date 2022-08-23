#include <assert.h>

int foo(int *x) __CPROVER_ensures(__CPROVER_return_value == *x + 5)
{
  return *x + 5;
}

int main()
{
  int n = 10;
  assert(foo(&n) != 15);
  return 0;
}
