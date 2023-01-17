#include <assert.h>

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);
  // Needed because the string constant is in the global pool.
  __CPROVER_field_decl_global("field1", (_Bool)0);

  const char *str = "!Hello!";

  // Set shadow memory for some characters
  for(int i = 1; i < 6; ++i)
  {
    __CPROVER_set_field(&str[i], "field1", 1);
  }

  // Populate with pointers into string constant
  char *pointers[10];
  for(int i = 0; i < 7; ++i)
  {
    pointers[i] = &str[i];
  }

  // Check that we can read the string constant's shadow memory
  // through the pointers.
  assert(__CPROVER_get_field(pointers[0], "field1") == 0);
  assert(__CPROVER_get_field(pointers[1], "field1") == 1);
  assert(__CPROVER_get_field(pointers[2], "field1") == 1);
  assert(__CPROVER_get_field(pointers[3], "field1") == 1);
  assert(__CPROVER_get_field(pointers[4], "field1") == 1);
  assert(__CPROVER_get_field(pointers[5], "field1") == 1);
  assert(__CPROVER_get_field(pointers[6], "field1") == 0);
  assert(__CPROVER_get_field(pointers[7], "field1") == 0);
  assert(__CPROVER_get_field(pointers[8], "field1") == 0);
  assert(__CPROVER_get_field(pointers[9], "field1") == 0);
}
