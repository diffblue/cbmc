struct node
{
  int data;
  struct node *next;
};

// Deep reads into a lazily-created inductive structure work when intermediate
// pointers are bound to local variables (the inline expression head->next->data
// does not -- see the "Chained dereference expressions" limitation in
// doc/cprover-manual/memory-primitives.md). The chain is finite and bounded by
// --unwind. See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  struct node *head;
  __CPROVER_assume(__CPROVER_rw_ok(head, sizeof(*head)));
  __CPROVER_assume(head != 0);

  // First-level scalar read.
  int d0 = head->data;
  __CPROVER_assert(d0 == d0, "first-level read");

  // Second- and third-level scalar reads via intermediate variables.
  struct node *second = head->next;
  if(second != 0)
  {
    int d1 = second->data;
    __CPROVER_assert(d1 == d1, "second-level read");

    struct node *third = second->next;
    if(third != 0)
    {
      int d2 = third->data;
      __CPROVER_assert(d2 == d2, "third-level read");
    }
  }
  return 0;
}
