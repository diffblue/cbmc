#include <assert.h>
#include <stdlib.h>

#define SIZE 8

void main()
{
  char *data = malloc(SIZE * sizeof(char));
  data[5] = 0;

  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    __CPROVER_assigns(i, __CPROVER_POINTER_OBJECT(data))
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      data[i] = 1;
    }

  assert(data[5] == 0);
  assert(data[5] == 1);
}
