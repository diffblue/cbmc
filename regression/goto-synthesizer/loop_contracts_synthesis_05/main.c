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
  __CPROVER_assume(b != NULL);

  b->data = malloc(SIZE);
  __CPROVER_assume(b->data != NULL);

  b->data[5] = 0;
  unsigned result = 0;

  unsigned arr[3] = {0, 0, 0};

  for(unsigned int i = 0; i < SIZE; i++)
  // clang-format off
  // __CPROVER_assigns(i, result)
  // clang-format on
  {
    result += 1;
  }

  for(unsigned int i = 0; i < SIZE; i++)
  // clang-format off
  // __CPROVER_assigns(i, arr[0])
  // clang-format on
  {
    arr[0] += 1;
  }

  for(unsigned j = 0; j < SIZE; j++)
  // __CPROVER_assigns(j, __CPROVER_POINTER_OBJECT(b->data))
  {
    for(unsigned i = 0; i < SIZE; i++)
    // clang-format off
    // __CPROVER_assigns(i, j, __CPROVER_POINTER_OBJECT(b->data))
    // clang-format on
    {
      b->data[i] = 1;
    }
  }
}
