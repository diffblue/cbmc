#include <assert.h>

struct STRUCTNAME
{
  int x1;
  int x2;
};

int main()
{
  __CPROVER_field_decl_local("field1", (char)0);

  struct STRUCTNAME n, m;
  int *p, *q;

  // Goto-symex is expected to create a case split for dereferencing p and q.
  int choice;
  __CPROVER_assume(choice > 0);
  if(choice)
  {
    p = &m.x1;
    q = &m.x2;
  }
  else
  {
    p = &n.x1;
    q = &n.x2;
  }

  assert(__CPROVER_get_field(&m.x1, "field1") == 0);
  assert(__CPROVER_get_field(&m.x2, "field1") == 0);
  assert(__CPROVER_get_field(p, "field1") == 0);
  assert(__CPROVER_get_field(q, "field1") == 0);

  __CPROVER_set_field(&m.x1, "field1", 2);
  assert(__CPROVER_get_field(&m.x1, "field1") == 2);
  assert(__CPROVER_get_field(&m.x2, "field1") == 0);
  assert(__CPROVER_get_field(p, "field1") == 2);
  assert(__CPROVER_get_field(q, "field1") == 0);

  __CPROVER_set_field(&m.x2, "field1", 3);
  assert(__CPROVER_get_field(&m.x1, "field1") == 2);
  assert(__CPROVER_get_field(&m.x2, "field1") == 3);
  assert(__CPROVER_get_field(p, "field1") == 2);
  assert(__CPROVER_get_field(q, "field1") == 3);

  __CPROVER_set_field(p, "field1", 4);
  assert(__CPROVER_get_field(&m.x1, "field1") == 4);
  assert(__CPROVER_get_field(&m.x2, "field1") == 3);
  assert(__CPROVER_get_field(p, "field1") == 4);
  assert(__CPROVER_get_field(q, "field1") == 3);

  __CPROVER_set_field(q, "field1", 5);
  assert(__CPROVER_get_field(&m.x1, "field1") == 4);
  assert(__CPROVER_get_field(&m.x2, "field1") == 5);
  assert(__CPROVER_get_field(p, "field1") == 4);
  assert(__CPROVER_get_field(q, "field1") == 5);

  assert(__CPROVER_get_field(&n.x1, "field1") == 0);
  assert(__CPROVER_get_field(&n.x2, "field1") == 0);
}
