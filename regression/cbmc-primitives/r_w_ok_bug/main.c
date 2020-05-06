#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p1;
  __CPROVER_assume(__CPROVER_r_ok(p1 - 1, 1));
  *p1;
}
