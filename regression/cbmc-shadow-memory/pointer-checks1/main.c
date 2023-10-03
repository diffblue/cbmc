#include <assert.h>

extern _Bool nondet();

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);

  char *buffer[10];

  __CPROVER_set_field(&buffer[9], "field1", 1);
  assert(__CPROVER_get_field(&buffer[9], "field1") == 1);
  __CPROVER_set_field(&buffer[10], "field1", 1);
  if(nondet())
  {
    assert(__CPROVER_get_field(&buffer[10], "field1") == 1);
  }
}
