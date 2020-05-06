#include <assert.h>
#include <stdlib.h>

char c1;

void main()
{
  char c2;

  char *p1 = &c1;
  assert(__CPROVER_r_ok(p1, 1));

  char *p2 = &c2;
  assert(__CPROVER_r_ok(p2, 1));

  char *p3 = malloc(1);
  __CPROVER_assume(p1 != NULL);
  assert(__CPROVER_r_ok(p3, 1));
}
