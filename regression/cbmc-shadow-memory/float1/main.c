#include <assert.h>

int main()
{
  __CPROVER_field_decl_local("field1", (unsigned __CPROVER_bitvector[7])0);

  float x;

  // Check that shadow memory has been initialized to zero.
  assert(!__CPROVER_get_field(&x, "field1"));

  // Check that shadow memory has been set to the chosen
  // nondeterministic value.
  unsigned __CPROVER_bitvector[7] v;
  __CPROVER_set_field(&x, "field1", v);
  assert(__CPROVER_get_field(&x, "field1") == v);
}
