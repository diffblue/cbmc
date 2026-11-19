#include <assert.h>

struct S
{
  unsigned a, b;
};

void main()
{
  unsigned i = 0;
  struct S s, c;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      __CPROVER_array_copy((char *)&c, (char *)&s);
      if(i > 0)
        assert(c.a == 0);
      s.a = i;
      s.b = i;
      i++;
    }
}
