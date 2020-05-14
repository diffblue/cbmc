#include <assert.h>

void main()
{
  char *p;
  assert(__CPROVER_POINTER_OFFSET(p) >= 0);
  assert(__CPROVER_POINTER_OFFSET(p) < 0);
}
