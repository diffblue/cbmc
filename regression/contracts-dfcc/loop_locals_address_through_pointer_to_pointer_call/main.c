#include <assert.h>
void check(unsigned **q, unsigned i)
{
  if(i > 0)
    assert(**q == 0);
}
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
      check(pp, i); /* callee reads previous t: must fail */
      t = i;
      i++;
    }
}
