#include <assert.h>
#include <string.h>

int src[10];

int main()
{
  __CPROVER_field_decl_local("field", (_Bool)0);
  __CPROVER_field_decl_global("field", (_Bool)0);

  assert(src[9] == 0);
  assert(__CPROVER_get_field(&(src[9]), "field") == 0);

  int dest[10];
  dest[9] = 1;
  assert(__CPROVER_get_field(&(dest[9]), "field") == 0);
  __CPROVER_set_field(&(dest[9]), "field", 1);
  assert(__CPROVER_get_field(&(dest[9]), "field") == 1);

  memcpy(dest, src, 10 * sizeof(int));
  assert(dest[9] == 0);
  assert(__CPROVER_get_field(&(src[9]), "field") == 0);
  assert(__CPROVER_get_field(&(dest[9]), "field") == 1);
}
