#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p;

  {
    char c;
    p = &c;
  }

  __CPROVER_assume(__CPROVER_r_ok(p, 1));
  assert(0); // fails
  *p;        // succeeds
}
