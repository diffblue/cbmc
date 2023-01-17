#include <assert.h>
#include <stdlib.h>

extern int nondet_int();

void main()
{
  __CPROVER_field_decl_global("field", (unsigned __CPROVER_bitvector[2])0);

  char *x = (char *)malloc((sizeof(char)) * 5l);

  assert(__CPROVER_get_field(x, "field") == 0);
  assert(__CPROVER_get_field(x + 1, "field") == 0);

  __CPROVER_set_field(x + 1, "field", 1);

  assert(__CPROVER_get_field(x, "field") == 0);
  assert(__CPROVER_get_field(x + 1, "field") == 1);
}
