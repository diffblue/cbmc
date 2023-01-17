#include <assert.h>
#include <stdlib.h>

extern int nondet_int();

void main()
{
  __CPROVER_field_decl_global("field", (unsigned __CPROVER_bitvector[2])0);

  static unsigned long int y;

  assert(__CPROVER_get_field(&y, "field") == 0);

  __CPROVER_set_field(&y, "field", 2u);
  assert(__CPROVER_get_field(&y, "field") == 2u);
}
