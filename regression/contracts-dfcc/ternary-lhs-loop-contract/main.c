#include <stdbool.h>
#include <stdlib.h>

void foo(int a, int b)
{
  char arr1[10];
  char arr2[10];
  char arr3[10];
  int i = 0;

  while(i < 10)
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    {
      ((a > 0) ? arr1 : b > 0 ? arr2 : arr3)[i] = 0;
      i++;
    }
}

int main()
{
  int a;
  int b;
  foo(a, b);
  return 0;
}
