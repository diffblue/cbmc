#include <assert.h>

struct P
{
  unsigned *q;
};

void check(struct P *s, unsigned i)
{
  if(i > 0)
    assert(*s->q == 0);
}

void main()
{
  unsigned i = 0, t;
  struct P s;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      s.q = &t;
      check(&s, i);
      t = i;
      i++;
    }
}
