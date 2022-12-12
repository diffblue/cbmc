#include <stdbool.h>
#include <stdlib.h>

// type of functions that manipulate arrays
typedef void (*arr_fun_t)(char *arr, size_t size);

// A contract for the arr_fun_t type
// requires a fresh array and positive size
// resets the first element to zero
void arr_fun_contract(char *arr, size_t size)
  // clang-format off
__CPROVER_requires(0 < size && __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr[0])
__CPROVER_ensures(arr[0] == 0)
  // clang-format on
  ;

// Testing pre-conditions constructs
// Takes a function pointer as input, uses it if its preconditions are met
// to establish post-conditions
int foo(char *arr, size_t size, arr_fun_t arr_fun)
  // clang-format off
__CPROVER_requires(arr == NULL || __CPROVER_is_fresh(arr, size))
__CPROVER_requires(__CPROVER_obeys_contract(arr_fun, arr_fun_contract))
__CPROVER_assigns(arr && size > 0 : arr[0])
__CPROVER_ensures((__CPROVER_return_value == 0) ==> (arr[0] == 0))
// clang-format on
{
  int retval = -1;
  if(arr && size > 0)
  {
  CALL:
    arr_fun(arr, size);
    retval = 0;
  }
  return retval;
}

void main()
{
  size_t size;
  char *arr;
  arr_fun_t fun;
  foo(arr, size, fun);
}
