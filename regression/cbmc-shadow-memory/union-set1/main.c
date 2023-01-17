#include <assert.h>

union UNIONNAME
{
  int x1;
  struct
  {
    char y1;
    // char padding;
    short y2;
    short y3;
  } x2;
  char x3[3];
};

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);

  union UNIONNAME u;

  __CPROVER_set_field(&u, "field1", (_Bool)1);
  assert(__CPROVER_get_field(&u.x1, "field1"));
  assert(__CPROVER_get_field((((char *)&u.x1) + 1), "field1"));
  assert(__CPROVER_get_field((((char *)&u.x1) + 2), "field1"));
  assert(__CPROVER_get_field((((char *)&u.x1) + 3), "field1"));
  assert(__CPROVER_get_field(&u.x2, "field1"));
  assert(__CPROVER_get_field(&u.x2.y1, "field1"));
  assert(__CPROVER_get_field(&u.x2.y2, "field1"));
  assert(__CPROVER_get_field((((char *)&u.x2.y2) + 1), "field1"));
  assert(__CPROVER_get_field(&u.x2.y3, "field1"));
  assert(__CPROVER_get_field((((char *)&u.x2.y3) + 1), "field1"));
  assert(__CPROVER_get_field(&u.x3[0], "field1"));
  assert(__CPROVER_get_field(&u.x3[1], "field1"));
  assert(__CPROVER_get_field(&u.x3[2], "field1"));

  __CPROVER_set_field(&u.x2, "field1", (_Bool)0);
  assert(!__CPROVER_get_field(&u.x1, "field1"));
  assert(!__CPROVER_get_field((((char *)&u.x1) + 1), "field1"));
  assert(!__CPROVER_get_field((((char *)&u.x1) + 2), "field1"));
  assert(!__CPROVER_get_field((((char *)&u.x1) + 3), "field1"));
  assert(!__CPROVER_get_field(&u.x2, "field1"));
  assert(!__CPROVER_get_field(&u.x2.y1, "field1"));
  assert(!__CPROVER_get_field(&u.x2.y2, "field1"));
  assert(!__CPROVER_get_field((((char *)&u.x2.y2) + 1), "field1"));
  assert(!__CPROVER_get_field(&u.x2.y3, "field1"));
  assert(!__CPROVER_get_field((((char *)&u.x2.y3) + 1), "field1"));
  assert(!__CPROVER_get_field(&u.x3[0], "field1"));
  assert(!__CPROVER_get_field(&u.x3[1], "field1"));
  assert(!__CPROVER_get_field(&u.x3[2], "field1"));
  return 0;
}
