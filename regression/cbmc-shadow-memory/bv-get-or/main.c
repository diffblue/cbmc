#include <assert.h>

int main()
{
  __CPROVER_field_decl_local("uninitialized", (_Bool)0);
  __CPROVER_field_decl_global("uninitialized", (_Bool)0);

  int i;
  char *a = &i;

  __CPROVER_set_field(a + 1, "uninitialized", 1);

  assert(__CPROVER_get_field(a, "uninitialized") == 0);
  assert(__CPROVER_get_field(a + 1, "uninitialized") == 1);
  assert(__CPROVER_get_field(&i, "uninitialized") == 1);
  // Expecting the remaining bytes to be untouched by the setting of the field.
  assert(__CPROVER_get_field(a + 2, "uninitialized") == 0);
  assert(__CPROVER_get_field(a + 3, "uninitialized") == 0);
}
