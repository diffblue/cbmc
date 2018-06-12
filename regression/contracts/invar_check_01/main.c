// invar_check_01

// This test checks that a basic loop invariant can be proven and used in
// combination with the negation of the loop guard to get a result.

#include <assert.h>

int main()
{
  int r;
  __CPROVER_assume(r >= 0);
  while(r > 0)
    __CPROVER_loop_invariant(r >= 0)
  {
    --r;
  }
  assert(r == 0);

  return 0;
}
