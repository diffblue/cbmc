#include <assert.h>
#include <stdlib.h>

#ifndef NULL
#  define NULL ((void *)0)
#endif

struct list;

typedef struct list list_nodet;

list_nodet fill_node(signed int depth_tag_list);

struct list
{
  int datum;
  struct list *next;
};

int max_depth = 4;

list_nodet *build_node(int depth)
{
  if(max_depth < depth)
    return ((list_nodet *)NULL);
  else
  {
    // previous CBMC would work with this line:
    // list_nodet *result = malloc(sizeof(struct list));
    // but not this:
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
  assert(i == 5);
  return 0;
}
