#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p = malloc(1);
  __CPROVER_assume(__CPROVER_POINTER_OBJECT(p) == 2);
  assert(0); // fails as expected

  // same value as the malloc'd pointer above
  char *q = (char *)((size_t)2 << sizeof(char *) * 8 - 8);

  *p = 1;
  *q = 2;

  assert(*p == 1); // currently succeeds
}
