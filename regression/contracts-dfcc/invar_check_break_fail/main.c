#include <assert.h>

int main()
{
  int r;
  __CPROVER_assume(r >= 0);

  while(r > 0)
    __CPROVER_loop_invariant(r >= 0)
    {
      --r;
      if(r <= 1)
      {
        break;
      }
      else
      {
        --r;
      }
    }

  assert(r == 0);

  return 0;
}
