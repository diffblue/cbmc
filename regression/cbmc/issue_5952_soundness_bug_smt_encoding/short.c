#include <assert.h>
#include <stdlib.h>

void main()
{
  char *data;
  data = nondet() ? malloc(1) : malloc(2);
  assert(__CPROVER_OBJECT_SIZE(data) <= 2);
}
