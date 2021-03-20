#include <assert.h>
#include <stdlib.h>

void main()
{
  char *data = malloc(1);
  *data = 42;

  unsigned i;
  while(i > 0)
    __CPROVER_loop_invariant(*data == 42)
    {
      *data = 42;
      i--;
    }

  assert(*data = 42);
}
