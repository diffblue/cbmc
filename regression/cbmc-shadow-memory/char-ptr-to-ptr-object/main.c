#include <stdlib.h>

int main()
{
  __CPROVER_field_decl_global("f", (_Bool)0);
  int x;
  int **q = malloc(sizeof(int *));
  __CPROVER_assume(q);
  *q = &x;
  // A pointer-typed object accessed through a character pointer.
  __CPROVER_set_field((unsigned char *)q, "f", 1);
  __CPROVER_assert(__CPROVER_get_field((unsigned char *)q, "f") == 1, "set");
  __CPROVER_assert(__CPROVER_get_field((unsigned char *)q, "f") == 0, "unset");
  return 0;
}
