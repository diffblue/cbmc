#include <stdlib.h>

void main()
{
  assert(NULL != (NULL + 1));
  assert(NULL != (NULL - 1));

  int offset;
  __CPROVER_assume(offset != 0);
  assert(NULL != (NULL + offset));

  assert(NULL - NULL == 0);

  int *ptr;
  assert(ptr - NULL == 0);
  ptr = NULL;
  assert((ptr - 1) + 1 == NULL);

  ptr = nondet() ? NULL : malloc(1);
  assert((ptr - 1) + 1 == (NULL + 1) - 1);
}
