#include <assert.h>

int main()
{
  int r;
  int s = 1;
  __CPROVER_assume(r >= 0);
  while(r > 0)
    // clang-format off
    __CPROVER_loop_invariant(r >= 0)
    __CPROVER_decreases(r)
    // clang-format on
    {
      r--;
    }
  assert(r == 0);
  assert(s == 1);

  return 0;
}
