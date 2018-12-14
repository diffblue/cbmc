#include <assert.h>

void test(int *arr)
{
  // works because the arrays we generate have at least one element
  arr[0] = 5;

  // doesn't work because our arrays have at most ten elements
  arr[10] = 10;
}
