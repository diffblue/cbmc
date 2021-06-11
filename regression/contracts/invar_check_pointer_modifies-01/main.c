#include <assert.h>
#include <stdlib.h>

void main()
{
  char *data = malloc(1);
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

  assert(*data = 42);
}
