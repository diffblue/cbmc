#include <stdlib.h>

int *z;

void bar() __CPROVER_assigns(*z)
{
}

void foo() __CPROVER_assigns()
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
