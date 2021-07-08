#include <assert.h>

int main()
{
  int r1, s1 = 1;
  __CPROVER_assume(r1 >= 0);
  while(r1 > 0)
    __CPROVER_loop_invariant(r1 >= 0 && s1 == 1) __CPROVER_decreases(r1)
    {
      s1 = 1;
      r1--;
    }
  assert(r1 == 0);

  int r2, s2 = 1;
  __CPROVER_assume(r2 >= 0);
  while(r2 > 0)
    __CPROVER_assigns(r2, s2) __CPROVER_loop_invariant(r2 >= 0 && s2 == 1)
      __CPROVER_decreases(r2)
    {
      s2 = 1;
      r2--;
    }
  assert(r2 == 0);
  return 0;
}
