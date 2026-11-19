#include <assert.h>
#include <stdint.h>

void main()
{
  unsigned i = 0, t;
  while(i < 10)
    __CPROVER_loop_invariant(i <= 10)
    {
      uintptr_t bits;
      __CPROVER_assume((unsigned *)bits == &t);
      if(i > 0)
        assert(*(unsigned *)bits == 0);
      t = i;
      i++;
    }
}
