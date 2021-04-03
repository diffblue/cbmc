#include <stdlib.h>

void main()
{
  char *p;
  int choice;

  if(choice)
  {
    p = malloc(2);
  }
  else
  {
    p = malloc(3);
  }

  __CPROVER_assert(__CPROVER_r_ok(p, 2), "assertion __CPROVER_r_ok(p, 2)");
  __CPROVER_assert(!__CPROVER_r_ok(p, 2), "assertion !__CPROVER_r_ok(p, 2)");

  __CPROVER_assert(__CPROVER_r_ok(p, 3), "assertion __CPROVER_r_ok(p, 3)");
  __CPROVER_assert(!__CPROVER_r_ok(p, 3), "assertion !__CPROVER_r_ok(p, 3)");

  __CPROVER_assert(__CPROVER_r_ok(p, 4), "assertion __CPROVER_r_ok(p, 4)");
  __CPROVER_assert(!__CPROVER_r_ok(p, 4), "assertion !__CPROVER_r_ok(p, 4)");
}
