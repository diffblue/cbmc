#include <stdlib.h>

int main()
{
  char *p = malloc(sizeof(*p));
  char *q;

#pragma CPROVER check push
#pragma CPROVER check disable "pointer-primitive"
  // do not generate checks for the following statements
  if(__CPROVER_same_object(p, q))
  {
  }
#pragma CPROVER check pop

  // generate check and fail on the following statements
  if(__CPROVER_same_object(p, q))
  {
  }
}
