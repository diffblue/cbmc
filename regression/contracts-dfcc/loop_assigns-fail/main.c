#include <assert.h>
#include <stdlib.h>

#define SIZE 8

struct blob
{
  char *data;
};

void main()
{
  struct blob *b = malloc(sizeof(struct blob));
  b->data = malloc(SIZE);
  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      b->data[i] = 1;
    }
}
