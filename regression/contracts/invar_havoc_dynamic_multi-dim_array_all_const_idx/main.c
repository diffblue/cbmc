#include <assert.h>
#include <stdlib.h>

#define SIZE 8

void main()
{
  char ***data = malloc(SIZE * sizeof(char **));
  for(unsigned i = 0; i < SIZE; i++)
  {
    data[i] = malloc(SIZE * sizeof(char *));
    for(unsigned j = 0; j < SIZE; j++)
      data[i][j] = malloc(SIZE * sizeof(char));
  }

  data[1][2][3] = 0;
  data[4][5][6] = 0;

  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    __CPROVER_assigns(i, data[4][5][6])
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      data[4][5][6] = 1;
    }

  assert(data[4][5][6] == 0);
  assert(data[1][2][3] == 0);
}
