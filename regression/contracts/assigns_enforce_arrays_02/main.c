#include <assert.h>
#include <stdlib.h>

int *arr;

void f1(int *a, int len) __CPROVER_assigns(*a)
{
  a[0] = 0;
  a[5] = 5;
}

void f2(int *a, int len) __CPROVER_assigns(__CPROVER_POINTER_OBJECT(a))
{
  a[0] = 0;
  a[5] = 5;
  free(a);
}

int main()
{
  arr = malloc(100 * sizeof(int));
  f1(arr, 100);
  f2(arr, 100);
}
