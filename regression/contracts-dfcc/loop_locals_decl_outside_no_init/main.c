#include <assert.h>

void main()
{
  unsigned n;
  __CPROVER_assume(n > 3 && n < 100);
  unsigned i = 0;
  unsigned t;
  while(i < n)
    __CPROVER_loop_invariant(i <= n)
    {
      if(i > 0)
        assert(t == 0);
      t = i;
      i++;
    }
}
