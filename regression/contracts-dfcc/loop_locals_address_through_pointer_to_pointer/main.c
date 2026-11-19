#include <assert.h>
void main()
{
  unsigned i = 0, t;
  unsigned *p;
  unsigned **pp;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      p = &t;
      pp = &p;
      if(i > 0)
        assert(**pp == 0); /* reads previous iteration's t: must fail */
      t = i;
      i++;
    }
}
