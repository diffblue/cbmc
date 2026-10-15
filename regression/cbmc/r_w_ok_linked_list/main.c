#include <assert.h>

struct node
{
  int data;
  struct node *next;
};

int list_length(struct node *head)
{
  int count = 0;
  struct node *curr = head;
  while(curr != 0)
  {
    count++;
    curr = curr->next;
  }
  return count;
}

int main()
{
  struct node *head;
  __CPROVER_assume(__CPROVER_rw_ok(head, sizeof(*head)));
  __CPROVER_assume(head != 0);

  int len = list_length(head);
  // With --unwind 4, the list can have at most 3 nodes
  assert(len >= 1);
  assert(len <= 3);
}
