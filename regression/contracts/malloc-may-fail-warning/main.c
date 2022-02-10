#include <stdlib.h>

void main()
{
  int *p = malloc(sizeof(int));
  __CPROVER_assert(p != NULL, "malloc-may-fail is not set");
}
