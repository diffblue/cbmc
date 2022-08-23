#include <stdio.h>

void bar(int *l) __CPROVER_assigns(*l) __CPROVER_requires(l != NULL)
  __CPROVER_ensures(__CPROVER_old(*l) == *l)
{
}

void foo(int *n) __CPROVER_assigns(*n) __CPROVER_requires(n != NULL)
  __CPROVER_ensures(__CPROVER_old(*n) == *n)
{
  bar(n);
}

int main()
{
  int m;
  foo(&m);

  return 0;
}
