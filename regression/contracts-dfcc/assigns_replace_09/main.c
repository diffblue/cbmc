#include <stdlib.h>

int *z;

void bar() __CPROVER_assigns(*z)
{
}

static void foo() __CPROVER_assigns(*z)
{
  bar();
}

int main()
{
  int x;
  z = &x;
  foo();
  return 0;
}
