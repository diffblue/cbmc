#include <stdlib.h>

int foo(char *arr1, char *arr2, size_t size)
  // clang-format off
__CPROVER_frees(size > 0 && arr1: arr1; arr2)
// clang-format on
{
  // the body does not actually free the function
  // since we are only testing parsing and typechecking
  return 0;
}

int main()
{
  size_t size;
  char *arr1 = malloc(size);
  char *arr2 = malloc(size);
  foo(arr1, arr2, size);
  return 0;
}
