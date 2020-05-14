#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p1 = malloc(1);
  char *p2 = malloc(1);

  assert(!__CPROVER_same_object(p1, p2));
}
