#include <assert.h>
struct P
{
  unsigned *q;
};
struct P g;
void main()
{
  unsigned i = 0, t;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      g.q = &t;
      if(i > 0)
        assert(*g.q == 0); /* reads previous t: must fail */
      t = i;
      i++;
    }
}
