#include <stdlib.h>

int main()
{
  char *p = malloc(sizeof(*p));
  char *q;

#pragma CPROVER check push
#pragma CPROVER check enable "pointer-primitive"
  // must generate checks
  if(__CPROVER_same_object(p, q))
  {
  }
#pragma CPROVER check push
#pragma CPROVER check disable "pointer-primitive"
  // must not generate checks
  if(__CPROVER_same_object(p, q))
  {
  }
#pragma CPROVER check push
#pragma CPROVER check enable "pointer-primitive"
  // must generate checks
  if(__CPROVER_same_object(p, q))
  {
  }
#pragma CPROVER check pop
  // must not generate generate checks
  if(__CPROVER_same_object(p, q))
  {
  }
#pragma CPROVER check pop
  // must generate generate checks
  if(__CPROVER_same_object(p, q))
  {
  }
#pragma CPROVER check pop
  // must not generate generate checks
  if(__CPROVER_same_object(p, q))
  {
  }
  return 0;
}
