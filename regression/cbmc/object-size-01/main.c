#include <assert.h>
#include <stdlib.h>

void main()
{
  char *p = malloc(1);
  free(p);

  assert(__CPROVER_OBJECT_SIZE(p) == 1);
  assert(__CPROVER_OBJECT_SIZE(p) != 1);

  {
    char c;
    p = &c;
  }

  assert(__CPROVER_OBJECT_SIZE(p) == 1);
  assert(__CPROVER_OBJECT_SIZE(p) != 1);
}
