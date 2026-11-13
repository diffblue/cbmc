struct node
{
  int data;
  struct node *next;
};

// Chained dereferences into a lazily-created inductive structure can be used
// directly: the nested-dereference lifting pass (on by default) hoists the
// intermediate pointers into temporaries, so guarded reads such as
// head->next->data verify. The chain is finite and bounded by --unwind.
// See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  struct node *head;
  __CPROVER_assume(__CPROVER_rw_ok(head, sizeof(*head)));
  __CPROVER_assume(head != 0);

  // First-level scalar read.
  __CPROVER_assert(head->data == head->data, "first-level read");

  // Second- and third-level scalar reads via inline chained dereferences.
  if(head->next != 0)
  {
    __CPROVER_assert(head->next->data == head->next->data, "second-level read");

    if(head->next->next != 0)
    {
      __CPROVER_assert(
        head->next->next->data == head->next->next->data, "third-level read");
    }
  }
  return 0;
}
