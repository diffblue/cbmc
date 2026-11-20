#include <assert.h>

unsigned *nondet_pointer();

unsigned *get_pointer()
{
  return nondet_pointer();
}

void main()
{
  unsigned i = 0, t;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      unsigned *p = get_pointer();
      __CPROVER_assume(p == &t);
      if(i > 0)
        assert(*p == 0);
      t = i;
      i++;
    }
}
