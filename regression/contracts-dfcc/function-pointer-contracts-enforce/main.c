#include <stdbool.h>
#include <stdlib.h>

bool nondet_bool();

// type of functions that manipulate arrays
typedef void (*arr_fun_t)(char *arr, size_t size);

// A contract for the arr_fun_t type
// requires a fresh array and positive size
// resets the first element to zero
void arr_fun_contract(char *arr, size_t size)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(arr, size) && size > 0)
__CPROVER_assigns(arr[0])
__CPROVER_ensures(arr[0] == 0)
// clang-format on
{
}

arr_fun_t bar()
  // clang-format off
 __CPROVER_ensures_contract(__CPROVER_return_value, arr_fun_contract)
// clang-format on
{
  // return a function that satisfies the contract
  return arr_fun_contract;
}

// Testing pre-conditions constructs
// Takes a function pointer as input, uses it if its preconditions are met
int foo(char *arr, size_t size, arr_fun_t arr_fun)
  // clang-format off
__CPROVER_requires_contract(arr_fun, arr_fun_contract)
__CPROVER_requires(arr == NULL || __CPROVER_is_fresh(arr, size))
__CPROVER_assigns(arr && size > 0: arr[0])
__CPROVER_ensures(arr && size > 0 ==> (arr[0] == 0 && __CPROVER_return_value == 0))
__CPROVER_ensures(!(arr && size > 0) ==> __CPROVER_return_value == -1)
// clang-format on
{
  if(nondet_bool())
    arr_fun = bar(); // non-deterministically get a function pointer from bar()

  int retval = -1;
  if(arr && size > 0) // check the preconditions of the function pointer
  {
    // calls the function pointer to do update the array
    arr_fun(arr, size);
    retval = 0;
  }
  // the post conditions of foo are established thanks to the post conditions
  // of arr_fun
  return retval;
}

void main()
{
  size_t size;
  char *arr;
  arr_fun_t arr_fun;
  // The precondition that `arr_fun` obeys `arr_fun`
  // and that bar returns a function that obeys `arr_fun`
  // are used establish the post-conditions of `foo`
  foo(arr, size, arr_fun);
}
