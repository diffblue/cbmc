#include <assert.h>
struct S
{
  unsigned *q;
};
void main()
{
  unsigned i = 0, t;
  struct S s;
  unsigned *p;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      s.q = &t;
      p = s.q; /* alias analysis: unknown origin */
      if(i > 0)
        assert(*p == 0); /* reads previous t: must fail */
      t = i;
      i++;
    }
}
