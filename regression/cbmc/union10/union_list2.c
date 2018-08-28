#include <assert.h>

struct list_item
{
  unsigned value;
  struct list_item *previous;
};

struct List
{
  unsigned something;
  struct list_item * index, end;
};

union U
{
  struct List my_list;
};

int main()
{
  union U u;

  u.my_list.index = &u.my_list.end;
  struct list_item *p0 = u.my_list.index;
  u.my_list.end.value = 123;
  u.my_list.end.previous = u.my_list.index;
  struct list_item *p1 = u.my_list.index;
  struct list_item *p2 = p1->previous;
  assert(p2 != 0); // should pass
}
