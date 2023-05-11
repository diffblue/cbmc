#include <assert.h>
#include <stdlib.h>

#define SIZE 8

void main()
{
  char data[SIZE];
  data[1] = 0;
  data[4] = 0;

  for(unsigned i = 0; i < SIZE; i++)
    __CPROVER_loop_invariant(i <= SIZE)
    {
      data[1] = i;
    }

  assert(data[1] == 0 || data[1] == 1);
  assert(data[4] == 0);
}
