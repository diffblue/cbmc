#include <stdlib.h>

int f(int *a) __CPROVER_ensures(1) __CPROVER_assigns()
{
  a = (int *)malloc(sizeof(int));
  *a = 5;
}

int main()
{
  int m = 4;
  f(&m);

  return 0;
}
