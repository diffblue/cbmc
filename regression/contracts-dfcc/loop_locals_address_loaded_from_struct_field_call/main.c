#include <assert.h>
struct S
{
  unsigned *q;
};
void check(unsigned *q, unsigned i)
{
  if(i > 0)
    assert(*q == 0);
}
void main()
{
  unsigned i = 0, t;
  struct S s;
  unsigned *p;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      s.q = &t;
      p = s.q;
      check(p, i); /* callee reads previous t: must fail */
      t = i;
      i++;
    }
}
