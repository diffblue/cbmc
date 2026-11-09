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

  // Assume we've got a node in this list!
  struct List *node;
  __CPROVER_assume(__CPROVER_is_sentinel_dll(&head, &tail, node));

  // do unrelated assignment, but to a node type
  struct List *other_node = 0;

  // check it's still a node
  __CPROVER_assert(__CPROVER_is_sentinel_dll(&head, &tail, node), "property 1");

  return 0;
}
