#include <assert.h>
unsigned **saved;
void save(unsigned **pp)
{
  saved = pp;
}
void check(unsigned i)
{
  if(i > 0)
    assert(**saved == 0);
} /* reads previous t */
void main()
{
  unsigned i = 0, t;
  unsigned *p = 0;
  save(&p); /* &p escapes before the loop */
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      p = &t;
      check(i); /* must fail */
      t = i;
      i++;
    }
}
