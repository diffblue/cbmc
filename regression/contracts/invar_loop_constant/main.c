// invar_loop_constant

// This test checks to see whether loop invariant checking discards sufficiently
// little information to be aware after the loop that s is necessarily 1.
// This test currently fails due to excessive havocking in checking loop
// invariants, but is not an obstacle to soundness of contract checking.

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
