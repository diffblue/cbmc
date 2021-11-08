#include <stdlib.h>

int main()
{
  int *p = malloc(sizeof(int));
  free(p);
  __CPROVER_assume(__CPROVER_r_ok(p, sizeof(int)));
  __CPROVER_assert(0, "should be unreachable");
}
