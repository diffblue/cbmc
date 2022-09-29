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
  head.p = 0;
  tail.n = 0;
  tail.p = &head;

  __CPROVER_assert(__CPROVER_is_sentinel_dll(&head, &tail), "property 1");

  return 0;
}
