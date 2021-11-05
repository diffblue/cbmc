#include <stdlib.h>

int main()
{
  char *p = malloc(sizeof(*p));
  char *q;

#pragma CPROVER check push
#pragma CPROVER check enable "pointer-overflow"
#pragma CPROVER check enable "pointer-overflow" // should not print an error message
#pragma CPROVER check push
#pragma CPROVER check disable "pointer-primitive"
#pragma CPROVER check enable "pointer-primitive" // should print an error message
#pragma CPROVER check pop
#pragma CPROVER check pop
  return 0;
}
