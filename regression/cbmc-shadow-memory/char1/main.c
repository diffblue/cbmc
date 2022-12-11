#include <assert.h>

// Add some string constants to confuse the value sets.
const char *x1 = "This is a short string constant";
const char *x2 = "This is a loooooooooooooonger string constant";
const char *x3 = "And yet another string constant";

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);
  __CPROVER_field_decl_global("field1", (_Bool)0);

  // Add some string constants to confuse the value sets.
  const char *y1 = "Yes, this is a short string constant";
  const char *y2 = "Yes, this is a loooooooooooooonger string constant";
  const char *y3 = "Yes, and yet another string constant";

  char *a;
  assert(__CPROVER_get_field(a, "field1") == 0);
  assert(__CPROVER_get_field(&a, "field1") == 0);
  // Cannot set because a doesn't point anywhere.
  __CPROVER_set_field(a, "field1", 1);
  // Hence, the value is still 0.
  assert(__CPROVER_get_field(a, "field1") == 0);
  assert(__CPROVER_get_field(&a, "field1") == 0);

  __CPROVER_set_field(a, "field1", 0);
  __CPROVER_set_field(&a, "field1", 1);
  assert(__CPROVER_get_field(a, "field1") == 0);
  assert(__CPROVER_get_field(&a, "field1") == 1);

  char *b = (char *)0;
  assert(__CPROVER_get_field(b, "field1") == 0);
  assert(__CPROVER_get_field(&b, "field1") == 0);
  // Cannot set because b points to NULL.
  __CPROVER_set_field(b, "field1", 1);
  // Hence, the value is still 0.
  assert(__CPROVER_get_field(b, "field1") == 0);
  assert(__CPROVER_get_field(&b, "field1") == 0);

  __CPROVER_set_field(b, "field1", 0);
  __CPROVER_set_field(&b, "field1", 1);
  assert(__CPROVER_get_field(b, "field1") == 0);
  assert(__CPROVER_get_field(&b, "field1") == 1);

  static char *c;
  assert(__CPROVER_get_field(c, "field1") == 0);
  assert(__CPROVER_get_field(&c, "field1") == 0);
  // Cannot set because c doesn't point anywhere.
  __CPROVER_set_field(c, "field1", 1);
  // Hence, the value is still 0.
  assert(__CPROVER_get_field(c, "field1") == 0);
  assert(__CPROVER_get_field(&c, "field1") == 0);

  __CPROVER_set_field(c, "field1", 0);
  __CPROVER_set_field(&c, "field1", 1);
  assert(__CPROVER_get_field(c, "field1") == 0);
  assert(__CPROVER_get_field(&c, "field1") == 1);
}
