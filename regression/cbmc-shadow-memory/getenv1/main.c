#include <stdlib.h>

void main()
{
  __CPROVER_field_decl_global("dr_write", (_Bool)0);

  char *env = getenv("PATH");
  __CPROVER_assume(env != NULL);
  assert(!__CPROVER_get_field(env, "dr_write"));

  __CPROVER_set_field(env, "dr_write", 1);
  assert(__CPROVER_get_field(env, "dr_write"));
}
