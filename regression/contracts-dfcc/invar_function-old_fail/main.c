#include <assert.h>

void main()
{
  int *x, y, z;

  x = &z;

  while(y > 0)
    __CPROVER_loop_invariant(*x == __CPROVER_old(*x))
    {
      --y;
      *x = *x + 1;
      *x = *x - 1;
    }
  assert(*x == z);
}
