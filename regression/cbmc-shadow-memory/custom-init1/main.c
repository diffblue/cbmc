#include <assert.h>
#include <stdlib.h>

struct STRUCTNAME
{
  int x1;
  int B1[3];
};

// Test initialization of various data types with custom values
int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)1);
  __CPROVER_field_decl_local("field2", (unsigned __CPROVER_bitvector[6])33);
  __CPROVER_field_decl_global("field1", (_Bool)1);
  __CPROVER_field_decl_global("field2", (unsigned __CPROVER_bitvector[6])33);

  int y;
  assert(__CPROVER_get_field(&y, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&y) + 1, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&y) + 2, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&y) + 3, "field1") == 1);
  assert(__CPROVER_get_field(&y, "field1") == 1);
  assert(__CPROVER_get_field(&y, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&y) + 1, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&y) + 2, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&y) + 3, "field2") == 33);

  int A[5];
  assert(__CPROVER_get_field(&A[2], "field1") == 1);
  assert(__CPROVER_get_field(((char *)&A[2]) + 1, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&A[2]) + 2, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&A[2]) + 3, "field1") == 1);
  assert(__CPROVER_get_field(&A[2], "field1") == 1);
  assert(__CPROVER_get_field(&A[2], "field2") == 33);
  assert(__CPROVER_get_field(((char *)&A[2]) + 1, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&A[2]) + 2, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&A[2]) + 3, "field2") == 33);

  struct STRUCTNAME m;
  assert(__CPROVER_get_field(&m.B1[1], "field1") == 1);
  assert(__CPROVER_get_field(((char *)&m.B1[1]) + 1, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&m.B1[1]) + 2, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&m.B1[1]) + 3, "field1") == 1);
  assert(__CPROVER_get_field(&m.B1[1], "field1") == 1);
  assert(__CPROVER_get_field(&m.B1[1], "field2") == 33);
  assert(__CPROVER_get_field(((char *)&m.B1[1]) + 1, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&m.B1[1]) + 2, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&m.B1[1]) + 3, "field2") == 33);

  struct STRUCTNAME n[3];
  assert(__CPROVER_get_field(&n[2].x1, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&n[2].x1) + 1, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&n[2].x1) + 2, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&n[2].x1) + 3, "field1") == 1);
  assert(__CPROVER_get_field(&n[2].x1, "field1") == 1);
  assert(__CPROVER_get_field(&n[2].x1, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&n[2].x1) + 1, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&n[2].x1) + 2, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&n[2].x1) + 3, "field2") == 33);

  short *z = malloc(10 * sizeof(short));
  assert(__CPROVER_get_field(&z[7], "field1") == 1);
  assert(__CPROVER_get_field(((char *)&z[7]) + 1, "field1") == 1);
  assert(__CPROVER_get_field(&z[7], "field2") == 33);
  assert(__CPROVER_get_field(((char *)&z[7]) + 1, "field2") == 33);

  struct STRUCTNAME *p = malloc(sizeof(struct STRUCTNAME));
  assert(__CPROVER_get_field(&p->B1[1], "field1") == 1);
  assert(__CPROVER_get_field(((char *)&p->B1[1]) + 1, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&p->B1[1]) + 2, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&p->B1[1]) + 3, "field1") == 1);
  assert(__CPROVER_get_field(&p->B1[1], "field1") == 1);
  assert(__CPROVER_get_field(&p->B1[1], "field2") == 33);
  assert(__CPROVER_get_field(((char *)&p->B1[1]) + 1, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&p->B1[1]) + 2, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&p->B1[1]) + 3, "field2") == 33);

  struct STRUCTNAME *u = malloc(3 * sizeof(struct STRUCTNAME));
  assert(__CPROVER_get_field(&u[2].x1, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&u[2].x1) + 1, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&u[2].x1) + 2, "field1") == 1);
  assert(__CPROVER_get_field(((char *)&u[2].x1) + 3, "field1") == 1);
  assert(__CPROVER_get_field(&u[2].x1, "field1") == 1);
  assert(__CPROVER_get_field(&u[2].x1, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&u[2].x1) + 1, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&u[2].x1) + 2, "field2") == 33);
  assert(__CPROVER_get_field(((char *)&u[2].x1) + 3, "field2") == 33);

  const char *w = "A string constant";
  assert(__CPROVER_get_field(&w[0], "field1") == 1);
  assert(__CPROVER_get_field(&w[5], "field1") == 1);
  assert(__CPROVER_get_field(&w[0], "field2") == 33);
  assert(__CPROVER_get_field(&w[5], "field2") == 33);
}
