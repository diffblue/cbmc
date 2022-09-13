#include <assert.h>
#include <stdlib.h>

#define SIZE 5

struct blob
{
  char *data;
};

void main()
{
  struct blob *b = malloc(sizeof(struct blob));
  b->data = malloc(SIZE);
  b->data[0] = 0;
  b->data[1] = 0;
  b->data[2] = 0;
  b->data[3] = 0;
  b->data[4] = 0;

  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    __CPROVER_assigns(i, __CPROVER_object_from(b->data))
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      // must pass
      b->data[i] = 1;
    }

  // these should all fail
  assert(b->data[0] == 0);
  assert(b->data[1] == 0);
  assert(b->data[2] == 0);
  assert(b->data[3] == 0);
  assert(b->data[4] == 0);
}
