struct linked_list
{
  struct linked_list *next;
};

void test(struct linked_list *list)
{
  assert(list);
  assert(list->next);
  assert(!list->next);
}
