#include <assert.h>
#include <stdbool.h>

const int MIN = 0;
const int MAX = 10;

bool f_state_invariant();

bool f_state_transition(int old_state, int return_value)
{
  return;
}

int f()
  // clang-format off
__CPROVER_assigns()

// state invariant: state variable is in [MIN,MAX]
__CPROVER_requires(
  MIN <= __CPROVER_ID "f::1::a" && __CPROVER_ID "f::1::a" <= MAX)
__CPROVER_ensures(
  MIN <= __CPROVER_ID "f::1::a" && __CPROVER_ID "f::1::a" <= MAX)

// state tansition: state var is either incremented or stays the same
__CPROVER_ensures(
  (__CPROVER_ID "f::1::a" == __CPROVER_old(__CPROVER_ID "f::1::a") + 1) ||
  (__CPROVER_ID "f::1::a" == __CPROVER_old(__CPROVER_ID "f::1::a")))

// state var value is returned
__CPROVER_ensures(__CPROVER_ID "f::1::a" == __CPROVER_return_value)
// clang-format on
{
  static int a = 0;
  if(a < MAX)
    a++;
  return a;
}

int main()
{
  f();
  return 0;
}
