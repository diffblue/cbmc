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
  char *old_data123 = &(data[1][2][3]);

  for(unsigned i = 0; i < SIZE; i++)
    __CPROVER_loop_invariant(i <= SIZE)
    {
      data[i][(i + 1) % SIZE][(i + 2) % SIZE] = 1;
    }

  assert(__CPROVER_same_object(old_data123, &(data[1][2][3])));
  assert(data[1][2][3] == 0);
}
