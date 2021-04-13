#include <assert.h>
#include <stdlib.h>

#define SIZE 8

void main()
{
  char *data = malloc(SIZE * sizeof(char));
  data[5] = 0;

  for(unsigned i = 0; i < SIZE; i++)
    __CPROVER_loop_invariant(i <= SIZE)
    {
      data[i] = 1;
    }

  assert(data[5] == 0);
  assert(data[5] == 1);
}
