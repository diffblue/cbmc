#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p = NULL;
  assert(!__CPROVER_r_ok(p, 10));
}
