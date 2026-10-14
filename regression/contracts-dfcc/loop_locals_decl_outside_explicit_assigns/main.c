#include <assert.h>

void main()
{
  unsigned n;
  __CPROVER_assume(n > 3 && n < 100);
  unsigned i = 0;
  unsigned t;
  while(i < n)
    // clang-format off
    __CPROVER_assigns(i)
    __CPROVER_loop_invariant(i <= n)
    // clang-format on
    {
      if(i > 0)
        assert(t == 0);
      t = i;
      i++;
    }
}
