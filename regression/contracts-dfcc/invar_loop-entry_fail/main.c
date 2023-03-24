#include <assert.h>

void main()
{
  int x, y, z;
  x = z;

  while(y > 0)
    __CPROVER_loop_invariant(x == __CPROVER_loop_entry(x))
    {
      --y;
      x = x + 1;
      x = x - 2;
    }
}
