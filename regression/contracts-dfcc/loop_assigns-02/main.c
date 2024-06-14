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
  if(b == NULL)
    return;
  b->data = malloc(SIZE);
  if(b->data == NULL)
    return;

  b->data[5] = 0;
  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    __CPROVER_assigns(i, b->data[i])
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      b->data[i] = 1;
    }

  assert(b->data[5] == 0);
}
