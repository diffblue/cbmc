#include <stdlib.h>

int main()
{
  int x;
  int *y = &x;
  int *z = &x;

  if(x)
  {
    y++;
  }
  else
  {
    z++;
  }

  __CPROVER_assume(y >= z);
  __CPROVER_assert(x != y, "x != y: expected successful");
  __CPROVER_assert(x == y, "x == y: expected failure");

  __CPROVER_assume(z >= x);

  __CPROVER_assert(z >= x, "z >= x: expected successful");
  __CPROVER_assert(z <= y, "z <= y: expected successful");
  __CPROVER_assert(z <= x, "z <= x: expected failure");
}
