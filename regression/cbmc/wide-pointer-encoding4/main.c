// Test for issue #2117: address reuse after free
#include <stdlib.h>
void main()
{
  int *x = malloc(sizeof(int));
  free(x);
  int *y = malloc(sizeof(int));
  if(x == y)
  {
    __CPROVER_assert(0, "reachable: malloc returned same address after free");
  }
  free(y);
}
