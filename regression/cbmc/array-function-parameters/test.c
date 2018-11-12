#include <assert.h>
#include <stdlib.h>

typedef struct Node_T Node_T;

struct Node_T
{
  int val;
  struct Node_T *next;
};

struct Test
{
  Node_T *lists[4];
};

void test(struct Test Test)
{
  assert(Test.lists[1]->next);
}
