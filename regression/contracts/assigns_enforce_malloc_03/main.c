#include <stdlib.h>

void foo() __CPROVER_assigns()
{
  char *loc1 = malloc(1);
  char *loc2 = malloc(1);
  int c;
  if(c)
    *loc1 = 0;
  else
    *loc2 = 0;
}

int main()
{
  foo();
  return 0;
}
