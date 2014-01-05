// from SV-COMP, based on code found in the Linux kernel

#include <stdlib.h>

struct list_head {
	struct list_head *next, *prev;
};

struct node {
    int                         value;
    struct list_head            linkage;
    struct list_head            nested;
};

struct list_head gl_list = { &gl_list, &gl_list };

int main()
{
  _Bool maybe_dynamic;

  struct node X;
  struct node *N = maybe_dynamic ? malloc(sizeof(struct node)) : &X;
  if (!N)
    return 1;

  N->value = 42;
	gl_list.prev=&N->linkage;
	N->linkage.next=&gl_list;
	N->linkage.prev=&gl_list;
	gl_list.next=&N->linkage;
  // we have:
  // gl_list.prev=&D->linkage;
  // D->linkage.next=&gl_list
  // D->linkage.prev=&gl_list;
  // gl_list.next=&D->linkage;

	N->nested.next = &(N->nested);
  N->nested.prev = &(N->nested);

  const struct list_head *head=&gl_list;

  // go one step backward
  head = head->prev;
  // we have:
  // head=&D->linkage

  // resolve root
  const struct node *node =
    (struct node *) ((char *)(head) -
                     (unsigned long)(&((struct node *)0)->linkage));
  // we have:
  // node=&D (==&D->value)
  __CPROVER_assert(node == N, "");
  __CPROVER_assert(head == N->linkage.next->prev, "");
  __CPROVER_assert(head == N->linkage.prev->next, "");
  __CPROVER_assert(head == node->linkage.next->prev, "");
  __CPROVER_assert(head == node->linkage.prev->next, "");

  return 0;
}
