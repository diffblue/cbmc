#include <assert.h>
#include <stdlib.h>

// type of functions that manipulate arrays
typedef void (*arr_fun_t)(char *arr, size_t size);

// A contract for the arr_fun_t type
void arr_fun_contract(char *arr, size_t size)
  // clang-format off
__CPROVER_requires(size > 0 && __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr[0])
__CPROVER_ensures(arr[0] == 0)
  // clang-format on
  ;

arr_fun_t get_arr_fun()
  // clang-format off
__CPROVER_ensures(
  __CPROVER_obeys_contract(__CPROVER_return_value, arr_fun_contract))
  // clang-format on
  ;

void foo(char *arr, size_t size)
  // clang-format off
__CPROVER_requires(size > 0 && __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr[0])
__CPROVER_ensures(arr[0] == 0)
// clang-format on
{
  // obtain function pointer from provider
  arr_fun_t arr_fun = get_arr_fun();
  // use it
CALL:
  arr_fun(arr, size);
}

void main()
{
  char *arr;
  size_t size;
  foo(arr, size);
}
