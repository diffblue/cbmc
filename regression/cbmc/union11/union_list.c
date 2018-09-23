#include <assert.h>

struct list_item
{
  // there could be more members here, this single one suffices to demonstrate
  // the problem/fix
  struct list_item *previous;
};

struct List
{
  // an element such that the offset of "index" is non-zero
  unsigned something;
  struct list_item *index;
  struct list_item end;
};

union U
{
  // there could be more members here, this single one suffices to demonstrate
  // the problem/fix
  struct List my_list;
};

int main()
{
  union U u;

  u.my_list.index = &(u.my_list.end);
  u.my_list.end.previous = u.my_list.index;
  struct list_item *p1 = u.my_list.index;
  struct list_item *p2 = p1->previous;
  struct list_item *p3 = p2->previous;
  assert(p3 != 0); // should pass
}
