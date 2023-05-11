#include <assert.h>

int main()
{
  int r;
  int s = 1;
  __CPROVER_assume(r >= 0);
  while(r > 0)
    __CPROVER_loop_invariant(r >= 0)
    {
      s = 1;
      r--;
    }
  assert(r == 0);
  assert(s == 1);

  return 0;
}
