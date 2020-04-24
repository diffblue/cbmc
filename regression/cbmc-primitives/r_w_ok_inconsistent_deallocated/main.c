#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p = malloc(1);
  free(p);

  __CPROVER_assume(__CPROVER_r_ok(p, 1));
  assert(0); // fails
  *p;        // succeeds
}
