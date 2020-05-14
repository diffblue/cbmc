#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p = malloc(10);
  char *q = p + 5;

  assert(__CPROVER_same_object(p, q));
}
