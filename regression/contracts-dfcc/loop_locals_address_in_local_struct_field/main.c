#include <assert.h>
struct P
{
  unsigned *q;
};
void main()
{
  unsigned i = 0, t;
  struct P s;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      s.q = &t;
      if(i > 0)
        assert(*s.q == 0); /* direct deref of a local struct field */
      t = i;
      i++;
    }
}
