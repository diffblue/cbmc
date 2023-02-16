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
  b->data[1] = 1;
  b->data[2] = 2;
  b->data[3] = 3;
  b->data[4] = 4;

  char *start = b->data;
  char *end = b->data + SIZE;

  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    __CPROVER_assigns(i,
      __CPROVER_object_upto(b->data, SIZE),
      __CPROVER_typed_target(b->data))
    __CPROVER_loop_invariant(
      i <= SIZE &&
      start <= b->data && b->data < end)
    // clang-format on
    {
      b->data = b->data; // must pass
      *(b->data) = 0;    // must pass
    }

  // must pass
  assert(start <= b->data && b->data <= end);
  // must fail
  assert(b->data == start);
}
