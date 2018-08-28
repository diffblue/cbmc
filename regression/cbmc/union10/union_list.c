#include <assert.h>

struct list_item
{
  struct list_item * previous;
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

int main() {
  union U u;

  u.my_list.index = &( u.my_list.end );
  u.my_list.end.previous = u.my_list.index;
  struct list_item *p1 = u.my_list.index;
  struct list_item *p2 = p1->previous;
  struct list_item *p3 = p2->previous;
  assert(p3!=0); // should pass
}
