#include <stdlib.h>

int main()
{
  __CPROVER_field_decl_global("f", (_Bool)0);
  int x;
  int **q = malloc(sizeof(int *));
  __CPROVER_assume(q);
  *q = &x;
  // The bytes of a pointer-typed object accessed as an array of characters.
  unsigned char(*bytes)[sizeof(int *)] = (unsigned char(*)[sizeof(int *)])q;
  __CPROVER_set_field(bytes, "f", 1);
  __CPROVER_assert(__CPROVER_get_field(bytes, "f") == 1, "set");
  __CPROVER_assert(
    __CPROVER_get_field((unsigned char *)q + 3, "f") == 1, "inner byte set");
  __CPROVER_assert(__CPROVER_get_field(bytes, "f") == 0, "unset");
  return 0;
}
