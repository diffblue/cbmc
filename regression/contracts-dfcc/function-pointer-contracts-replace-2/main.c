#include <stdlib.h>

// Type of functions that manipulate arrays of a given size
typedef void (*arr_fun_t)(char *arr, size_t size);

// A contract for the arr_fun_t type
void arr_fun_contract(char *arr, size_t size)
  // clang-format off
  __CPROVER_requires(size > 0 && __CPROVER_is_fresh(arr, size))
  __CPROVER_assigns(arr[0]) __CPROVER_ensures(arr[0] == 0)
  // clang-format on
  ;

// Uses a function pointer
int foo(char *arr, size_t size, arr_fun_t arr_fun)
  // clang-format off
__CPROVER_requires(arr ==> __CPROVER_is_fresh(arr, size))
__CPROVER_requires(
  arr_fun ==> __CPROVER_obeys_contract(arr_fun, arr_fun_contract))
__CPROVER_assigns(arr && size > 0 && arr_fun: arr[0])
__CPROVER_ensures(__CPROVER_return_value ==> (arr[0] == 0))
// clang-format on
{
  if(arr && size > 0 && arr_fun)
  {
  CALL:
    arr_fun(arr, size);
    return 1;
  }
  return 0;
}

// returns function pointer satisfying arr_fun_contract
arr_fun_t get_arr_fun()
  // clang-format off
__CPROVER_ensures(
  __CPROVER_obeys_contract(__CPROVER_return_value, arr_fun_contract))
  // clang-format on
  ;

// allocates an array and uses get_arr_fun and foo to initialise it
char *bar(size_t size)
  // clang-format off
__CPROVER_ensures(
  __CPROVER_return_value ==> size > 0 &&
  __CPROVER_is_fresh(__CPROVER_return_value, size) &&
  __CPROVER_return_value[0] == 0)
// clang-format on
{
  if(size > 0)
  {
    char *arr;
    arr = malloc(size);
    if(arr && foo(arr, size, get_arr_fun()))
      return arr;

    return NULL;
  }
  return NULL;
}

void main()
{
  size_t size;
  char *arr = bar(size);
}
