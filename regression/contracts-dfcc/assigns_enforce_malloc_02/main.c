#include <stdlib.h>

int f(int n, int *ptr) __CPROVER_assigns()
{
  while(n > 0)
  {
    ptr = (int *)malloc(sizeof(int));
    // this is OK because writes
    // only happen on freshly allocated
    // object and not the initial
    // object b was pointing to
    *ptr = 5;
    n--;
  }
}

int main()
{
  int b = 3;
  f(5, &b);

  return 0;
}
