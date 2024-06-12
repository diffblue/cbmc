#include <assert.h>
#include <stdlib.h>

_Bool nondet_bool();

void main()
{
  char *data;
  data = nondet_bool() ? malloc(1) : malloc(2);
  assert(__CPROVER_OBJECT_SIZE(data) <= 2);
}
