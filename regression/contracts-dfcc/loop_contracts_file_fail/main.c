#include <assert.h>
#include <stdlib.h>

#define SIZE 8

struct blob
{
  char *data;
};

void main()
{
  foo();
}

void foo()
{
  struct blob *b = malloc(sizeof(struct blob));
  b->data = malloc(SIZE);

  b->data[5] = 0;
  for(unsigned i = 0; i < SIZE; i++)
  // clang-format off
  // clang-format on
  {
    b->data[i] = 1;
  }
}

void foo1()
{
  struct blob *b = malloc(sizeof(struct blob));
  b->data = malloc(SIZE);

  b->data[5] = 0;
  for(unsigned i = 0; i < SIZE; i++)
  // clang-format off
  // clang-format on
  {
    b->data[i] = 1;
  }
}
