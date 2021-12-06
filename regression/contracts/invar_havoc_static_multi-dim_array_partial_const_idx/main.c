#include <assert.h>
#include <stdlib.h>

#define SIZE 8

void main()
{
  char data[SIZE][SIZE][SIZE];

  data[1][2][3] = 0;
  data[4][5][6] = 0;

  for(unsigned i = 0; i < SIZE; i++)
    __CPROVER_assigns(i, __CPROVER_POINTER_OBJECT(data))
      __CPROVER_loop_invariant(i <= SIZE)
    {
      data[4][i][6] = 1;
    }

  assert(data[1][2][3] == 0);
  assert(data[4][5][6] == 0);
}
