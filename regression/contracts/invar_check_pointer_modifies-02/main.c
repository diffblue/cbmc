#include <assert.h>
#include <stdlib.h>

void main()
{
  char *copy, *data = malloc(1);

  copy = data;
  *data = 42;

  unsigned i;
  while(i > 0)
    // clang-format off
    __CPROVER_loop_invariant(*data == 42)
    __CPROVER_decreases(i)
    // clang-format on
    {
      *data = 42;
      i--;
    }

  assert(data == copy);
  assert(*copy = 42);
}
