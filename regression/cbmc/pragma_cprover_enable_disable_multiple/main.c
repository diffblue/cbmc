#include <stdlib.h>

int main()
{
  char *p = malloc(sizeof(*p));
  char *q;

#pragma CPROVER check push
#pragma CPROVER check enable "pointer-overflow"
// should not print an error message
#pragma CPROVER check enable "pointer-overflow"
#pragma CPROVER check push
#pragma CPROVER check disable "pointer-primitive"
// PARSE_ERROR
#pragma CPROVER check enable "pointer-primitive"
#pragma CPROVER check pop
#pragma CPROVER check pop
  return 0;
}
