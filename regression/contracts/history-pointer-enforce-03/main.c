#include <limits.h>

void foo(int *x) __CPROVER_assigns(*x)
  __CPROVER_requires(*x > 0 && *x < INT_MAX - 5) __CPROVER_ensures(
    *x >= __CPROVER_old(*x) + 4 && *x <= __CPROVER_old(*x) + 6)
{
  *x = *x + 5;
}

int main()
{
  int n;
  foo(&n);

  return 0;
}
