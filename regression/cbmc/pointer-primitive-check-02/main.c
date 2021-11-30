#include <stdlib.h>

char *p1;

void main()
{
  __CPROVER_r_ok(p1, 1);

  char *p2 = NULL;
  __CPROVER_r_ok(p2, 1);
}
