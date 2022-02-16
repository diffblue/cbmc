#include <stdlib.h>

int x;
int *z = &x;

void bar() __CPROVER_assigns(*z)
{
}

static void foo() __CPROVER_assigns(*z)
{
  bar();
}

int main()
{
  foo();
  return 0;
}
