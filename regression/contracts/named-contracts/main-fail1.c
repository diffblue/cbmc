#include <stdlib.h>

int foo(int *arr, size_t size)
{
  return 0;
}

int foo(int *arr, size_t size)
  // clang-format off
__CPROVER_requires(size > 0 && __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(
  arr[0], arr[size-1]; 
  size >= 10: arr[5];
)
__CPROVER_ensures(arr[0] == 0 && arr[size-1] == 0)
__CPROVER_ensures(size >= 10 ==> arr[5] == __CPROVER_return_value)
  // clang-format on
  ;

int main()
{
  int retval = foo(&arr, 10);
  return 0;
}
