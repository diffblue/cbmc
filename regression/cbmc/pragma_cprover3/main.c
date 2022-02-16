#include <stdlib.h>

int main()
{
  char *p = malloc(sizeof(*p));
  char *q;

#pragma CPROVER check push
#pragma CPROVER check disable "pointer-primitive"
  // do not generate checks for the following statements
  if(__CPROVER_r_ok(p, sizeof(*p) + 2))
  {
  }
#pragma CPROVER check pop

  // no checks are generated for the following statement as the behaviour is
  // always defined
  if(__CPROVER_same_object(p, q))
  {
  }

  // generate check and fail on the following statements
  if(__CPROVER_r_ok(q, 1))
  {
  }
}
