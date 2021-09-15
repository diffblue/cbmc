#include <stdlib.h>

int x;
int *z = &x;

void bar() __CPROVER_assigns(*z)
{
}

void foo() __CPROVER_assigns()
{
  bar();
}

int main()
{
  foo();
  return 0;
}
