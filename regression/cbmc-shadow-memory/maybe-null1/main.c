#include <assert.h>
#include <stdlib.h>

void main()
{
  __CPROVER_field_decl_local("field1", (_Bool)1);
  int x;
  int *y = NULL;
  int c;
  int *z;

  // Goto-symex is expected to create a case split for dereferencing z.
  __CPROVER_assume(c > 0);
  if(c)
    z = &x;
  else
    z = y;

  // Check initialization
  assert(__CPROVER_get_field(z, "field1") == 1);

  // z actually points to x, which has valid shadow memory.
  __CPROVER_set_field(z, "field1", 0);
  assert(__CPROVER_get_field(z, "field1") == 0);
  assert(__CPROVER_get_field(&x, "field1") == 0);

  // y is NULL, which has no valid shadow memory
  // and thus returns the default value.
  assert(__CPROVER_get_field(y, "field1") == 1);
}
