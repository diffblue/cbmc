#include <assert.h>
#include <stdlib.h>

typedef struct list_nodet list_nodet;

struct list_nodet
{
  int val;
  struct list_nodet *next;
};

struct Test
{
  list_nodet *lists[4];
};

void test(struct Test Test)
{
  // array elements are nondet initialised (min-null-tree-depth is respected)
  assert(Test.lists[0]->next);
  assert(Test.lists[1]->next);
  assert(Test.lists[2]->next);
  assert(Test.lists[3]->next);

  // array elements are nondet initialised (max-nondet-tree-depth is respected)
  assert(!Test.lists[0]->next->next);
  assert(!Test.lists[1]->next->next);
  assert(!Test.lists[2]->next->next);
  assert(!Test.lists[3]->next->next);

  // array elements are not all initialised to the same size
  assert(Test.lists[0] != Test.lists[1]);
  assert(Test.lists[1] != Test.lists[2]);
  assert(Test.lists[2] != Test.lists[3]);

  assert(!Test.lists[4]);
}
