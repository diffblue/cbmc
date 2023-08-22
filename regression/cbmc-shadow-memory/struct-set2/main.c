#include <assert.h>

struct S
{
  short x[3];
  char c;
};

int main(void)
{
  __CPROVER_field_decl_local("f", (char)0);

  struct S s;

  // Setting the struct recursively set all its fields
  __CPROVER_set_field(&s, "f", 1);

  assert(__CPROVER_get_field(&s.x[0], "f") == 1);
  assert(__CPROVER_get_field(&s.x[1], "f") == 1);
  assert(__CPROVER_get_field(&s.x[2], "f") == 1);
  assert(__CPROVER_get_field(&s.c, "f") == 1);
  assert(__CPROVER_get_field(&s, "f") == 1);

  // Setting the struct recursively set all its fields
  __CPROVER_set_field(&s, "f", 0);

  assert(__CPROVER_get_field(&s.x[0], "f") == 0);
  assert(__CPROVER_get_field(&s.x[1], "f") == 0);
  assert(__CPROVER_get_field(&s.x[2], "f") == 0);
  assert(__CPROVER_get_field(&s.c, "f") == 0);
  assert(__CPROVER_get_field(&s, "f") == 0);

  // Setting a field of the struct changes its values ad after aggregation the whole struct value
  __CPROVER_set_field(&s.x[1], "f", 2);

  assert(__CPROVER_get_field(&s.x[0], "f") == 0);
  assert(__CPROVER_get_field(&s.x[1], "f") == 2);
  assert(__CPROVER_get_field(&s.x[2], "f") == 0);
  assert(__CPROVER_get_field(&s.c, "f") == 0);
  assert(__CPROVER_get_field(&s, "f") == 2);

  // Rest shadow memory
  __CPROVER_set_field(&s, "f", 0);

  // Changing ONLY first cell of S array at field x by using offset with pointer arithmetics
  short *p = ((short *)&s) + 1;
  __CPROVER_set_field(p, "f", 3);

  assert(__CPROVER_get_field(&s.x[0], "f") == 0);
  assert(__CPROVER_get_field(&s.x[1], "f") == 3);
  assert(__CPROVER_get_field(&s.x[2], "f") == 0);
  assert(__CPROVER_get_field(&s.c, "f") == 0);
  assert(__CPROVER_get_field(&s, "f") == 3);

  return 0;
}