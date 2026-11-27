#include <assert.h>

struct S
{
  unsigned a, b;
};

void main()
{
  unsigned i = 0;
  struct S s;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      if(i > 0)
        assert(s.b == 0);
      s.a = i;
      s.b = i;
      i++;
    }
}
