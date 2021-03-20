#include <assert.h>
#include <stdlib.h>

void main()
{
  char *copy, *data = malloc(1);

  copy = data;
  *data = 42;

  unsigned i;
  while(i > 0)
    __CPROVER_loop_invariant(*data == 42)
    {
      *data = 42;
      i--;
    }

  assert(data == copy);
  assert(*copy = 42);
}
