#include <assert.h>

void test(const char *str)
{
  // Set shadow memory for some characters
  for(int i = 1; i < 6; ++i)
  {
    __CPROVER_set_field(&str[i], "field1", 1);
  }

  // Copy string constant into buffer
  char buffer[10];
  for(int i = 0; i < 7; ++i)
  {
    buffer[i] = str[i];
    __CPROVER_set_field(
      &buffer[i], "field1", __CPROVER_get_field(&str[i], "field1"));
  }

  // Check that shadow memory has not been copied
  for(int i = 0; i < 7; ++i)
  {
    assert(__CPROVER_get_field(&buffer[0], "field1") == 0);
  }

  // Copy shadow memory
  for(int i = 0; i < 7; ++i)
  {
    __CPROVER_set_field(
      &buffer[i], "field1", __CPROVER_get_field(&str[i], "field1"));
  }

  // Check that shadow memory has been copied
  assert(__CPROVER_get_field(&buffer[0], "field1") == 0);
  assert(__CPROVER_get_field(&buffer[1], "field1") == 1);
  assert(__CPROVER_get_field(&buffer[2], "field1") == 1);
  assert(__CPROVER_get_field(&buffer[3], "field1") == 1);
  assert(__CPROVER_get_field(&buffer[4], "field1") == 1);
  assert(__CPROVER_get_field(&buffer[5], "field1") == 1);
  assert(__CPROVER_get_field(&buffer[6], "field1") == 0);
  assert(__CPROVER_get_field(&buffer[7], "field1") == 0);
  assert(__CPROVER_get_field(&buffer[8], "field1") == 0);
  assert(__CPROVER_get_field(&buffer[9], "field1") == 0);
}

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);
  // Needed because the string constant is in the global pool.
  __CPROVER_field_decl_global("field1", (_Bool)0);

  test("!Hello!");
}
