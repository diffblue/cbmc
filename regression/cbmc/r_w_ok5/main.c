#include <stdlib.h>

void main()
{
  char c[2];
  __CPROVER_assert(__CPROVER_r_ok(c, 2), "assertion __CPROVER_r_ok(c, 2)");
  __CPROVER_assert(!__CPROVER_r_ok(c, 2), "assertion !__CPROVER_r_ok(c, 2)");
  __CPROVER_assert(__CPROVER_r_ok(c, 3), "assertion __CPROVER_r_ok(c, 3)");
  __CPROVER_assert(!__CPROVER_r_ok(c, 3), "assertion !__CPROVER_r_ok(c, 3)");

  char *p = malloc(2);
  __CPROVER_assert(__CPROVER_r_ok(c, 2), "assertion __CPROVER_r_ok(c, 2)");
  __CPROVER_assert(!__CPROVER_r_ok(c, 2), "assertion !__CPROVER_r_ok(c, 2)");
  __CPROVER_assert(__CPROVER_r_ok(p, 3), "assertion __CPROVER_r_ok(p, 3)");
  __CPROVER_assert(!__CPROVER_r_ok(p, 3), "assertion !__CPROVER_r_ok(p, 3)");
}
