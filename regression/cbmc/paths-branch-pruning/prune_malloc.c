// Test that branch pruning handles malloc/free correctly.
// The conditional expressions in stdlib.c (our change) should not
// interfere with branch pruning.

#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int));
  if(p == 0)
    return 1;

  *p = 42;
  __CPROVER_assert(*p == 42, "written value");

  free(p);

  return 0;
}
