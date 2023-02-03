#include <assert.h>
#include <stdlib.h>

struct STRUCTNAME
{
  int x1;
  int B1[3];
};

void scalars_and_pointers_to_scalars()
{
  int y = 10;

  assert(__CPROVER_get_field(&y, "field1") == 0);
  assert(__CPROVER_get_field(&y, "field2") == 0);

  int *z;

  assert(__CPROVER_get_field(&z, "field1") == 0);
  assert(__CPROVER_get_field(&z, "field2") == 0);

  __CPROVER_set_field(&y, "field1", 3);
  __CPROVER_set_field(&y, "field2", 4);
  __CPROVER_set_field(&z, "field1", 5);
  __CPROVER_set_field(&z, "field2", 6);

  z = &y;

  assert(__CPROVER_get_field(z, "field1") == 3);
  assert(__CPROVER_get_field(z, "field2") == 4);

  assert(__CPROVER_get_field(&z, "field1") == 5);
  assert(__CPROVER_get_field(&z, "field2") == 6);

  assert(__CPROVER_get_field(z, "field1") == __CPROVER_get_field(&y, "field1"));
  assert(__CPROVER_get_field(z, "field2") == __CPROVER_get_field(&y, "field2"));

  int **w;

  w = &z;

  assert(__CPROVER_get_field(&w, "field1") == 0);
  assert(__CPROVER_get_field(&w, "field2") == 0);

  assert(__CPROVER_get_field(w, "field1") == 5);
  assert(__CPROVER_get_field(w, "field2") == 6);

  assert(__CPROVER_get_field(*w, "field1") == 3);
  assert(__CPROVER_get_field(*w, "field2") == 4);
}

void arrays_and_pointers_into_arrays()
{
  int A[5];

  z = &(A[4]);

  assert(__CPROVER_get_field(z, "field1") == 0);
  assert(__CPROVER_get_field(z, "field2") == 0);

  __CPROVER_set_field(&(A[3]), "field1", 13);
  __CPROVER_set_field(&(A[3]), "field2", 14);
  __CPROVER_set_field(z, "field1", 15);
  __CPROVER_set_field(z, "field2", 16);

  z = A;

  assert(__CPROVER_get_field(z + 3, "field1") == 13);
  assert(__CPROVER_get_field(z + 3, "field2") == 14);
  assert(__CPROVER_get_field(z + 4, "field1") == 15);
  assert(__CPROVER_get_field(z + 4, "field2") == 16);

  int i;
  __CPROVER_assume(0 <= i && i < 5);
  __CPROVER_set_field(&(A[i]), "field1", 42);
  assert(__CPROVER_get_field(&(A[i]), "field1") == 42);

  z = &(A[i]);
  __CPROVER_set_field(z, "field1", 43);
  assert(__CPROVER_get_field(z, "field1") == 43);
}

void structs_and_pointers_into_structs()
{
  struct STRUCTNAME m;
  struct STRUCTNAME *p;

  assert(__CPROVER_get_field(&p, "field1") == 0);
  __CPROVER_set_field(&p, "field1", 1);
  assert(__CPROVER_get_field(&p, "field1") == 1);

  p = &m;

  assert(__CPROVER_get_field(&(p->x1), "field1") == 0);
  assert(__CPROVER_get_field(&(p->B1[1]), "field2") == 0);

  __CPROVER_set_field(&((*p).x1), "field1", 2);
  __CPROVER_set_field(&((*p).B1[1]), "field2", 2);

  assert(__CPROVER_get_field(&(p->x1), "field1") == 2);
  assert(__CPROVER_get_field(&(p->B1[1]), "field2") == 2);
  assert(__CPROVER_get_field(&(p->B1[2]), "field1") == 0);

  int *q = &(m.B1[2]);
  assert(__CPROVER_get_field(q, "field1") == 0);
  __CPROVER_set_field(q, "field1", 7);
  assert(__CPROVER_get_field(q, "field1") == 7);

  int j;
  __CPROVER_assume(0 <= j && j < 3);
  __CPROVER_set_field(&(m.B1[j]), "field1", 44);
  assert(__CPROVER_get_field(&(m.B1[j]), "field1") == 44);

  z = &(m.B1[j]);
  __CPROVER_set_field(z, "field1", 45);
  assert(__CPROVER_get_field(z, "field1") == 45);
}

void arrays_of_structs_and_pointers_into_them()
{
  struct STRUCTNAME n[3];

  assert(__CPROVER_get_field(&(n[1].x1), "field1") == 0);
  assert(__CPROVER_get_field(&(n[1].B1[1]), "field2") == 0);

  p = &(n[2]);

  __CPROVER_set_field(&(n[1].x1), "field1", 1);
  __CPROVER_set_field(&(p->x1), "field1", 2);
  assert(__CPROVER_get_field(&(n[1].x1), "field1") == 1);
  assert(__CPROVER_get_field(&(p->x1), "field1") == 2);

  __CPROVER_set_field(&(n[1].B1[1]), "field2", 3);
  __CPROVER_set_field(&(p->B1[1]), "field2", 4);
  assert(__CPROVER_get_field(&(n[1].B1[1]), "field2") == 3);
  assert(__CPROVER_get_field(&(p->B1[1]), "field2") == 4);

  q = &(n[1].x1);
  assert(__CPROVER_get_field(q, "field1") == 1);
  __CPROVER_set_field(q, "field1", 5);
  assert(__CPROVER_get_field(q, "field1") == 5);

  q = &(n[1].B1[1]);
  assert(__CPROVER_get_field(q, "field2") == 3);
  __CPROVER_set_field(q, "field2", 6);
  assert(__CPROVER_get_field(q, "field2") == 6);

  int k;
  __CPROVER_assume(0 <= k && k < 3);
  __CPROVER_set_field(&(n[k].B1[j]), "field1", 46);
  assert(__CPROVER_get_field(&(n[k].B1[j]), "field1") == 46);

  z = &(n[k].B1[j]);
  __CPROVER_set_field(z, "field1", 47);
  assert(__CPROVER_get_field(z, "field1") == 47);
}

int main()
{
  __CPROVER_field_decl_local("field1", (char)0);
  __CPROVER_field_decl_local("field2", (__CPROVER_bitvector[6])0);

  scalars_and_pointers_to_scalars();
  arrays_and_pointers_into_arrays();
  structs_and_pointers_into_structs();
  arrays_of_structs_and_pointers_into_them();
}
