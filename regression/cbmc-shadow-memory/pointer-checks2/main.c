#include <assert.h>

int main()
{
  __CPROVER_field_decl_local("uninitialized", (char)0);

  char a;
  int *i = &a;

  __CPROVER_set_field(i, "uninitialized", 1); // should this fail?

  assert(__CPROVER_get_field(&a, "uninitialized") == 1);
  assert(__CPROVER_get_field(&a + 1, "uninitialized") == 1);
  assert(__CPROVER_get_field(i, "uninitialized") == 1);
}
