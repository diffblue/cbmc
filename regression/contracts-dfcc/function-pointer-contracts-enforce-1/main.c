#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

typedef int (*fun_t)(int);

int add_one(int x)
  __CPROVER_ensures(__CPROVER_return_value == __CPROVER_old(x) + 1);

int foo(fun_t f_in, int x, fun_t *f_out)
  // clang-format off
__CPROVER_requires_contract(f_in, add_one, NULL)
__CPROVER_assigns(f_out)
__CPROVER_ensures(f_in ==>__CPROVER_return_value == __CPROVER_old(x) + 1)
__CPROVER_ensures(!f_in ==>__CPROVER_return_value == __CPROVER_old(x))
__CPROVER_ensures_contract(*f_out, add_one, NULL)
// clang-format on
{
  *f_out = NULL;
  if(f_in)
  {
    *f_out = f_in;
    // this branch must be reachable
    __CPROVER_assert(false, "then branch is reachable, expecting FAILURE");
  CALL_F_IN:
    return f_in(x);
  }
  else
  {
    // this branch must be reachable
    __CPROVER_assert(false, "else branch is reachable, expecting FAILURE");
    return x;
  }
}

int main()
{
  fun_t f_in;
  int x;
  fun_t f_out;
  foo(f_in, x, &f_out);
  if(f_out)
  {
    __CPROVER_assert(false, "then branch is reachable, expecting FAILURE");
  CALL_F_OUT:
    __CPROVER_assert(f_out(1) == 2, "f_out satisfies add_one");
  }
  else
  {
    __CPROVER_assert(false, "else branch is reachable, expecting FAILURE");
  }
}
