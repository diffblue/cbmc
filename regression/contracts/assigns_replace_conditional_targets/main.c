#include <stdbool.h>

bool nz(int x)
{
  return x == 0;
}

int foo(bool a, int *x, int *y, char *z)
  // clang-format off
__CPROVER_requires(x && y && z)
__CPROVER_assigns(
   a && nz(*x): *x;
  !a && nz(*y): *y;
  !nz(*x) && !nz(*y): __CPROVER_POINTER_OBJECT(z);
)
__CPROVER_ensures(true)
// clang-format on
{
  if(!nz(*x) && !nz(*y))
    __CPROVER_havoc_object(z);

  if(a && x)
  {
    if(nz(*x))
      *x = 0;
  }

  if(~!a && y)
  {
    if(nz(*y))
      *y = 0;
  }

  return 0;
}

int main()
{
  bool a, old_a;
  old_a = a;

  int x, old_x;
  old_x = x;

  int y, old_y;
  old_y = y;

  char *z = malloc(1);
  *z = '0';

  foo(a, &x, &y, z);

  // check frame conditions
  // clang-format off
  __CPROVER_assert(old_a == a, "a unchanged, expecting SUCCESS");

  __CPROVER_assert(
    old_a && nz(old_x) ==> x == old_x, "x changed, expecting FAILURE");
  __CPROVER_assert(
    !(old_a && nz(old_x)) ==> x == old_x, "x unchanged, expecting SUCCESS");

  __CPROVER_assert(
    !old_a && nz(old_y) ==> y == old_y, "y changed, expecting FAILURE");
  __CPROVER_assert(
    !(!old_a && nz(old_y)) ==> y == old_y, "y unchanged, expecting SUCCESS");

  __CPROVER_assert(
    !(nz(old_x) || nz(old_y)) ==> *z == '0', "z changed, expecting FAILURE");
  __CPROVER_assert(
    nz(old_x) || nz(old_y) ==> *z == '0', "z unchanged, expecting SUCCESS");
  // clang-format on

  return 0;
}
