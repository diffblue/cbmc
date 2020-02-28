#include <assert.h>
#include <stdlib.h>

void main()
{
  char c[2];
  assert(__CPROVER_r_ok(c, 2));
  assert(!__CPROVER_r_ok(c, 2));
  assert(__CPROVER_r_ok(c, 3));
  assert(!__CPROVER_r_ok(c, 3));

  char *p = malloc(2);
  assert(__CPROVER_r_ok(c, 2));
  assert(!__CPROVER_r_ok(c, 2));
  assert(__CPROVER_r_ok(p, 3));
  assert(!__CPROVER_r_ok(p, 3));
}
