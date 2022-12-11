#include <assert.h>
#include <errno.h>

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);
  __CPROVER_field_decl_global("field1", (_Bool)0);

  int *error = __errno();

  assert(__CPROVER_get_field(error, "field1") == 0);

  __CPROVER_set_field(error, "field1", 1);
  assert(__CPROVER_get_field(error, "field1") == 1);
}
