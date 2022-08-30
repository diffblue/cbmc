#include <stdlib.h>

int foo(char *arr, int size)
  // clang-format off
__CPROVER_frees(size)
// clang-format on
{
  // the body does not actually free the array
  // since we are only testing parsing and typechecking
  return 0;
}

int main()
{
  size_t size;
  char *arr = malloc(size);
  foo(arr, size);
  return 0;
}
