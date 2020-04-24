#include <assert.h>

char *nondet();

void main()
{
  char *p = nondet();
  __CPROVER_assume(__CPROVER_r_ok(p, 10));
  assert(0); // fails
  *p;        // succeeds
}
