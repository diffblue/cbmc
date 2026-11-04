#include <assert.h>

// A function that DFCC does not instrument (here, through its `__VERIFIER`
// prefix), as a verification tool uses for the state of its own checks. Its
// writes are not checked against any write set.
void __VERIFIER_record(int *p)
{
  *p = 1;
}

int main()
{
  int x = 0;
  int y = 1;
  int *p = &x;
  for(int i = 0; i < 10; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    // clang-format on
    {
      *p = i;
      __VERIFIER_record(&y);
    }
  // The inferred write set of the loop is `i` and `*p`, which is `x`: `y` is
  // not havocked.
  assert(y == 1);
  return 0;
}
