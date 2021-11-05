#include <stdlib.h>

int main()
{
  char *p = malloc(sizeof(*p));
  char *q;

#pragma CPROVER check push
#pragma CPROVER check enable "pointer-primitive"
  // generate checks for the following statements and fail
  if(__CPROVER_same_object(p, q))
  {
  }
#pragma CPROVER check pop

  // but do not generate checks on the following statements
  if(__CPROVER_same_object(p, q))
  {
  }
}
