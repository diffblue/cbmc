#include <stdlib.h>

// A function defining a conditionally freeable target
__CPROVER_freeable_t
foo_frees(char *arr, const size_t size, const size_t new_size)
{
  __CPROVER_freeable(arr);
}

char *foo(char *arr, const size_t size, const size_t new_size)
  // clang-format off
 // error is_freed cannot be used in preconditions
__CPROVER_requires(!__CPROVER_is_freed(arr))
__CPROVER_requires(__CPROVER_is_freeable(arr))
__CPROVER_assigns(__CPROVER_whole_object(arr))
__CPROVER_frees(foo_frees(arr, size, new_size))
__CPROVER_ensures(
  (arr && new_size > size) ==>
    __CPROVER_is_fresh(__CPROVER_return_value, new_size))
__CPROVER_ensures(
  (arr && new_size > size) ==>
    __CPROVER_is_freed(__CPROVER_old(arr)))
__CPROVER_ensures(
    !(arr && new_size > size) ==>
      __CPROVER_return_value == __CPROVER_old(arr))
// clang-format on
{
  if(arr && new_size > size)
  {
    free(arr);
    return malloc(new_size);
  }
  else
  {
    return arr;
  }
}

int main()
{
  size_t size;
  size_t new_size;
  char *arr = malloc(size);
  arr = foo(arr, size, new_size);
  return 0;
}
