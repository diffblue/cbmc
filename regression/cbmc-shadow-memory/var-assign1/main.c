#include <assert.h>

int main()
{
  __CPROVER_field_decl_local("field", (char)0);

  char z;
  int x;
  __CPROVER_set_field(&x, "field", z);
  assert(__CPROVER_get_field(&x, "field") == z);
}
