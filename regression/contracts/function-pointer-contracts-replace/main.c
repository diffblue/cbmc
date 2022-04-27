#include <assert.h>
#include <stdlib.h>

// type of functions that manipulate arrays
typedef void (*arr_fun_t)(char *arr, size_t size);

// A contract for the arr_fun_t type
void contract(char *arr, size_t size)
  // clang-format off
__CPROVER_requires((size > 0 && __CPROVER_is_fresh(arr, size)))
__CPROVER_assigns(arr[0]) 
__CPROVER_ensures(arr[0] == 0)
// clang-format on
{
}

arr_fun_t foo(arr_fun_t infun, arr_fun_t *outfun)
  // clang-format off
__CPROVER_requires_contract(infun, contract)
__CPROVER_ensures_contract(*outfun, contract)
__CPROVER_ensures_contract(__CPROVER_return_value, contract)
// clang-format on
{
  *outfun = contract;
  return infun;
}

void main()
{
  // establish pre-conditions before replacement
  arr_fun_t infun = contract;

  arr_fun_t outfun1 = NULL;
  arr_fun_t outfun2 = foo(infun, &outfun1);

  // checking post-conditions after replacement
  assert(outfun1 == contract);
  assert(outfun2 == contract);
}
