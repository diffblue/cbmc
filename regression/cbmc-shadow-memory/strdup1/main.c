#include <assert.h>
#include <stdlib.h>
#include <string.h>

int main()
{
  __CPROVER_field_decl_local("field1", (unsigned __CPROVER_bitvector[2])0);
  __CPROVER_field_decl_global("field1", (unsigned __CPROVER_bitvector[2])0);

  char *s = (char *)malloc(3 * sizeof(char));
  assert(__CPROVER_get_field(&s[0], "field1") == 0);
  assert(__CPROVER_get_field(&s[1], "field1") == 0);

  __CPROVER_set_field(&s[0], "field1", 1);
  __CPROVER_set_field(&s[1], "field1", 1);
  assert(__CPROVER_get_field(&s[0], "field1") == 1);
  assert(__CPROVER_get_field(&s[1], "field1") == 1);

  // The shadow memories of the source and destination buffers
  // are independent.
  char *d = strdup(s);
  assert(__CPROVER_get_field(&s[0], "field1") == 1);
  assert(__CPROVER_get_field(&s[1], "field1") == 1);
  assert(__CPROVER_get_field(&d[0], "field1") == 0);
  assert(__CPROVER_get_field(&d[1], "field1") == 0);

  __CPROVER_set_field(&d[0], "field1", 2);
  __CPROVER_set_field(&d[1], "field1", 2);
  assert(__CPROVER_get_field(&d[0], "field1") == 2);
  assert(__CPROVER_get_field(&d[1], "field1") == 2);
  assert(__CPROVER_get_field(&s[0], "field1") == 1);
  assert(__CPROVER_get_field(&s[1], "field1") == 1);
}
