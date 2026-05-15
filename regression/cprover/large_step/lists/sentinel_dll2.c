// Modeled after the AWS C common doubly linked list.
// https://github.com/awslabs/aws-c-common/blob/main/include/aws/common/linked_list.h
// https://github.com/awslabs/aws-c-common/blob/main/include/aws/common/linked_list.inl

// The 'head' and 'tail' nodes are sentinel nodes, indicating the
// beginning and end of the list.

#include <stdlib.h>

struct List
{
  struct List *n, *p;
};

int main()
{
  struct List head, tail;

  // setup the empty list
  head.n = &tail;
  tail.p = &head;

  // now add one node at the end
  struct List new_node;
  new_node.n = &tail;
  new_node.p = tail.p;
  tail.p->n = &new_node;

  // check it's a node
  __CPROVER_assert(
    __CPROVER_is_sentinel_dll(&head, &tail, &new_node), "property 1");

  return 0;
}
