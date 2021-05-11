#include <assert.h>
#include <stdlib.h>

#ifdef _MSC_VER
#  define _Static_assert(x, m) static_assert(x, m)
#endif

struct list;

typedef struct list list_nodet;

list_nodet fill_node(signed int depth_tag_list);

struct list
{
  int datum;
  struct list *next;
};

int max_depth = 2;

list_nodet *build_node(int depth)
{
  if(max_depth < depth)
    return ((list_nodet *)NULL);
  else
  {
    _Static_assert(sizeof(list_nodet) == 16, "");
    list_nodet *result = malloc(16);

    if(result)
    {
      *result = fill_node(depth + 1);
    }
    return result;
  }
}

list_nodet fill_node(int depth)
{
  list_nodet result;
  result.datum = depth;
  result.next = build_node(depth);
  return result;
}

int main()
{
  list_nodet *node = build_node(0);
  int i = 0;
  list_nodet *list_walker = node;
  for(; list_walker; list_walker = list_walker->next)
  {
    i = i + 1;
  }
  assert(i == 3);
  return 0;
}
