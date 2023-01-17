#include <assert.h>

struct INNERSTRUCT
{
  int x1;
  char x2[2];
};

struct STRUCT
{
  struct INNERSTRUCT x[3];
  int y;
};

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);

  struct STRUCT s;
  __CPROVER_set_field(&s, "field1", (_Bool)1);
  assert(__CPROVER_get_field(&s.x[0], "field1"));
  assert(__CPROVER_get_field(&s.x[0].x1, "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[0].x1) + 1), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[0].x1) + 2), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[0].x1) + 3), "field1"));
  assert(__CPROVER_get_field(&s.x[0].x2[0], "field1"));
  assert(__CPROVER_get_field(&s.x[0].x2[1], "field1"));
  assert(__CPROVER_get_field(&s.x[1], "field1"));
  assert(__CPROVER_get_field(&s.x[1].x1, "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[1].x1) + 1), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[1].x1) + 2), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[1].x1) + 3), "field1"));
  assert(__CPROVER_get_field(&s.x[1].x2[0], "field1"));
  assert(__CPROVER_get_field(&s.x[1].x2[1], "field1"));
  assert(__CPROVER_get_field(&s.x[2], "field1"));
  assert(__CPROVER_get_field(&s.x[2].x1, "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[2].x1) + 1), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[2].x1) + 2), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[2].x1) + 3), "field1"));
  assert(__CPROVER_get_field(&s.x[2].x2[0], "field1"));
  assert(__CPROVER_get_field(&s.x[2].x2[1], "field1"));
  assert(__CPROVER_get_field(&s.y, "field1"));
  assert(__CPROVER_get_field((((char *)&s.y) + 1), "field1"));
  assert(__CPROVER_get_field((((char *)&s.y) + 2), "field1"));
  assert(__CPROVER_get_field((((char *)&s.y) + 3), "field1"));

  __CPROVER_set_field(&s.x[1], "field1", (_Bool)0);
  assert(__CPROVER_get_field(&s.x[0], "field1"));
  assert(__CPROVER_get_field(&s.x[0].x1, "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[0].x1) + 1), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[0].x1) + 2), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[0].x1) + 3), "field1"));
  assert(__CPROVER_get_field(&s.x[0].x2[0], "field1"));
  assert(__CPROVER_get_field(&s.x[0].x2[1], "field1"));
  assert(!__CPROVER_get_field(&s.x[1], "field1"));
  assert(!__CPROVER_get_field(&s.x[1].x1, "field1"));
  assert(!__CPROVER_get_field((((char *)&s.x[1].x1) + 1), "field1"));
  assert(!__CPROVER_get_field((((char *)&s.x[1].x1) + 2), "field1"));
  assert(!__CPROVER_get_field((((char *)&s.x[1].x1) + 3), "field1"));
  assert(!__CPROVER_get_field(&s.x[1].x2[0], "field1"));
  assert(!__CPROVER_get_field(&s.x[1].x2[1], "field1"));
  assert(__CPROVER_get_field(&s.x[2], "field1"));
  assert(__CPROVER_get_field(&s.x[2].x1, "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[2].x1) + 1), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[2].x1) + 2), "field1"));
  assert(__CPROVER_get_field((((char *)&s.x[2].x1) + 3), "field1"));
  assert(__CPROVER_get_field(&s.x[2].x2[0], "field1"));
  assert(__CPROVER_get_field(&s.x[2].x2[1], "field1"));
  assert(__CPROVER_get_field(&s.y, "field1"));
  assert(__CPROVER_get_field((((char *)&s.y) + 1), "field1"));
  assert(__CPROVER_get_field((((char *)&s.y) + 2), "field1"));
  assert(__CPROVER_get_field((((char *)&s.y) + 3), "field1"));
  return 0;
}
