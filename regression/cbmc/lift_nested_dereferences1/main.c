struct node
{
  int data;
  struct node *next;
};

// A chained dereference head->next->data reads the intermediate pointer
// head->next twice: once in the guard and once in the dereference. The
// nested-dereference lifting pass hoists it into a single temporary, so the
// guard and the dereference agree on the same value and the deep read
// verifies. With --no-lift-nested-dereferences the intermediate pointer is
// read (and lazily materialised) twice, and the dereference is reported as a
// spurious failure. See https://github.com/diffblue/cbmc/issues/7829
int main()
{
  struct node *head;
  __CPROVER_assume(__CPROVER_rw_ok(head, sizeof(*head)));
  __CPROVER_assume(head != 0);

  if(head->next != 0)
  {
    int d = head->next->data;
    __CPROVER_assert(d == d, "deep read via chained dereference");
  }
  return 0;
}
