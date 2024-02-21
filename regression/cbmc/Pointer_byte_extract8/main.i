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
    return ((list_nodet *)0);
  else
  {
    __CPROVER_assert(sizeof(list_nodet) == 16, "struct size is 16 bytes");
    list_nodet *result = __CPROVER_allocate(16, 0);

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
  __CPROVER_assert(i == 3, "i should be 3");
  return 0;
}
