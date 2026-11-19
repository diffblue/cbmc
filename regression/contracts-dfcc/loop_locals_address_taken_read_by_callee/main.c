#include <assert.h>

void check(unsigned *q, unsigned i)
{
  if(i > 0)
    assert(*q == 0);
}

void main()
{
  unsigned i = 0, t;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      check(&t, i);
      t = i;
      i++;
    }
}
