#include <assert.h>
#include <stdlib.h>

#define SIZE 8

struct blob
{
  char *data;
};

void main()
{
  int y;
  struct blob *b = malloc(sizeof(struct blob));
  b->data = malloc(SIZE);

  b->data[5] = 0;
  for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    __CPROVER_assigns(i, __CPROVER_POINTER_OBJECT(b->data))
    __CPROVER_loop_invariant(i <= SIZE)
    // clang-format on
    {
      b->data[i] = 1;

      int x;
      for(unsigned j = 0; j < i; j++)
        // clang-format off
        // y is not assignable by outer loop, so this should be flagged
        __CPROVER_assigns(j, y, x, b->data[i])
        __CPROVER_loop_invariant(j <= i)
        // clang-format on
        {
          x = b->data[j] * b->data[j];
          b->data[i] += x;
          y += j;
        }
    }

  assert(b->data[5] == 0);
}
