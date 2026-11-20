#include <assert.h>

unsigned *g;

void store(unsigned *q)
{
  g = q;
}

void check(unsigned i)
{
  if(i > 0)
    assert(*g == 0);
}

void main()
{
  unsigned i = 0, t;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      check(i);
      store(&t);
      t = i;
      i++;
    }
}
