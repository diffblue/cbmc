#include <assert.h>
struct P
{
  unsigned *q;
};
struct P *saved;
void save(struct P *s)
{
  saved = s;
}
void check(unsigned i)
{
  if(i > 0)
    assert(*saved->q == 0);
}
void main()
{
  unsigned i = 0, t;
  struct P s;
  save(&s); /* &s escapes before the loop */
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      s.q = &t;
      check(i); /* must fail */
      t = i;
      i++;
    }
}
