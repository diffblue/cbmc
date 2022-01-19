#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p = malloc(1);
  assert(__CPROVER_POINTER_OBJECT(p) == 1);

  assert(
    __CPROVER_same_object(p, (char *)((size_t)1 << (sizeof(char *) * 8 - 8))));
  assert(
    !__CPROVER_same_object(p, (char *)((size_t)2 << (sizeof(char *) * 8 - 8))));
}
