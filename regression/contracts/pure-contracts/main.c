#include <stdlib.h>

char foo(char *arr, size_t size)
  // clang-format off
__CPROVER_requires(
  0 < size && size < __CPROVER_max_malloc_size &&
  __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr[0], arr[size - 1]) 
__CPROVER_ensures(
  arr[0] == __CPROVER_return_value && arr[size - 1] == __CPROVER_return_value)
// clang-format on
{
  __CPROVER_pure_contract();
}

char bar(char *arr, size_t size)
  // clang-format off
__CPROVER_requires(
  0 < size && size < __CPROVER_max_malloc_size &&
  __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr[0], arr[size - 1]) 
__CPROVER_ensures(
  arr[0] == __CPROVER_return_value && arr[size - 1] == __CPROVER_return_value)
// clang-format on

{
  return foo(arr, size);
}

int main()
{
  size_t size;
  char *arr;
  bar(arr, size);
  return 0;
}
