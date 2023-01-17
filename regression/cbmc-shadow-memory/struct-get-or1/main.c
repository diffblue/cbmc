#include <assert.h>
#include <stdlib.h>

struct INNERSTRUCT
{
  int x1;
  int x2[2];
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

  __CPROVER_set_field(&(s.x[0].x1), "field1", 1);
  assert(__CPROVER_get_field(&s, "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[0]), "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[0].x1), "field1") == 1);
  // Not allowed: assert(__CPROVER_get_field(s.x[0].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[0].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[0].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[1].x1), "field1") == 0);
  // Not allowed: assert(__CPROVER_get_field(s.x[1].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[1].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[1].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x1), "field1") == 0);
  // Not allowed: assert(__CPROVER_get_field(s.x[2].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.y), "field1") == 0);

  __CPROVER_set_field(&(s.y), "field1", 1);
  assert(__CPROVER_get_field(&s, "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[0]), "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[0].x1), "field1") == 1);
  // Not allowed: assert(__CPROVER_get_field(s.x[0].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[0].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[0].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[1].x1), "field1") == 0);
  // assert(__CPROVER_get_field(s.x[1].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[1].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[1].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x1), "field1") == 0);
  // Not allowed: assert(__CPROVER_get_field(s.x[2].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.y), "field1") == 1);

  __CPROVER_set_field(&(s.x[1].x2[0]), "field1", 1);
  assert(__CPROVER_get_field(&s, "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[0]), "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[0].x1), "field1") == 1);
  // Not allowed: assert(__CPROVER_get_field(s.x[0].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[0].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[0].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[1].x1), "field1") == 0);
  // Not allowed: assert(__CPROVER_get_field(s.x[1].x2, "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[1].x2[0]), "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[1].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x1), "field1") == 0);
  // Not allowed: assert(__CPROVER_get_field(s.x[2].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.y), "field1") == 1);

  __CPROVER_set_field(&(s.x[2].x2[1]), "field1", 1);
  assert(__CPROVER_get_field(&s, "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[0]), "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[0].x1), "field1") == 1);
  // Not allowed: assert(__CPROVER_get_field(s.x[0].x2, "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[0].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[0].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[1].x1), "field1") == 0);
  // Not allowed: assert(__CPROVER_get_field(s.x[1].x2, "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[1].x2[0]), "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[1].x2[1]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x1), "field1") == 0);
  // Not allowed: assert(__CPROVER_get_field(s.x[2].x2, "field1") == 1);
  assert(__CPROVER_get_field(&(s.x[2].x2[0]), "field1") == 0);
  assert(__CPROVER_get_field(&(s.x[2].x2[1]), "field1") == 1);
  assert(__CPROVER_get_field(&(s.y), "field1") == 1);
}
