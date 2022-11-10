#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

typedef int (*fun_t)(int);

int add_one(int x)
  __CPROVER_ensures(__CPROVER_return_value == __CPROVER_old(x) + 1);

// returns either a pointer to a function that satisfies add_one or NULL
fun_t get_add_one()
  __CPROVER_ensures_contract(__CPROVER_return_value, add_one, NULL);

int foo(int x, fun_t *f_out)
  // clang-format off
__CPROVER_assigns(*f_out)
__CPROVER_ensures(
  __CPROVER_return_value == __CPROVER_old(x) + 1 ||
  __CPROVER_return_value == __CPROVER_old(x))
__CPROVER_ensures_contract(*f_out, add_one, NULL)
// clang-format on
{
  *f_out = NULL;
  // obtain a pointer to a function that satisfies add_one;
  fun_t f_in = get_add_one();
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
  int x;
  fun_t f_out;
  foo(x, &f_out);
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
