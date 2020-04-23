#include <stdlib.h>

char *p1;

void main()
{
  __CPROVER_POINTER_OBJECT(p1);

  char *p2 = NULL;
  __CPROVER_POINTER_OBJECT(p2);
}
