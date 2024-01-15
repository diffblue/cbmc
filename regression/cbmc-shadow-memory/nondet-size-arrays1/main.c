#include <assert.h>
#include <stdlib.h>

#ifdef _WIN32
void *alloca(size_t alloca_size);
#endif

int main()
{
  __CPROVER_field_decl_local("field1", (char)0);
  __CPROVER_field_decl_local("field2", (__CPROVER_bitvector[6])0);
  __CPROVER_field_decl_global("field1", (char)0);
  __CPROVER_field_decl_global("field2", (__CPROVER_bitvector[6])0);

  /***********************
   * Variable-size arrays
   ***********************/

  int n;
  __CPROVER_assume(5 <= n && n < 10);
  int A[n];

  int *z = &(A[4]);

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
  __CPROVER_assume(0 <= i && i < n);
  __CPROVER_set_field(&(A[i]), "field1", 42);
  assert(__CPROVER_get_field(&(A[i]), "field1") == 42);

  z = &(A[i]);
  __CPROVER_set_field(z, "field1", 43);
  assert(__CPROVER_get_field(z, "field1") == 43);

  /***********************
   * Variable-size arrays with malloc
   ***********************/

  int *B = malloc(n * sizeof(int));

  z = &(B[4]);

  assert(__CPROVER_get_field(z, "field1") == 0);
  assert(__CPROVER_get_field(z, "field2") == 0);

  __CPROVER_set_field(&(B[3]), "field1", 13);
  __CPROVER_set_field(&(B[3]), "field2", 14);
  __CPROVER_set_field(z, "field1", 15);
  __CPROVER_set_field(z, "field2", 16);

  z = B;

  assert(__CPROVER_get_field(z + 3, "field1") == 13);
  assert(__CPROVER_get_field(z + 3, "field2") == 14);
  assert(__CPROVER_get_field(z + 4, "field1") == 15);
  assert(__CPROVER_get_field(z + 4, "field2") == 16);

  int j;
  __CPROVER_assume(0 <= j && j < n);
  __CPROVER_set_field(&(B[j]), "field1", 42);
  assert(__CPROVER_get_field(&(B[j]), "field1") == 42);

  z = &(B[j]);
  __CPROVER_set_field(z, "field1", 43);
  assert(__CPROVER_get_field(z, "field1") == 43);

  /***********************
   * Variable-size arrays with alloca
   ***********************/

  int *C = alloca(n * sizeof(int));

  z = &(C[4]);

  assert(__CPROVER_get_field(z, "field1") == 0);
  assert(__CPROVER_get_field(z, "field2") == 0);

  __CPROVER_set_field(&(C[3]), "field1", 13);
  __CPROVER_set_field(&(C[3]), "field2", 14);
  __CPROVER_set_field(z, "field1", 15);
  __CPROVER_set_field(z, "field2", 16);

  z = C;

  assert(__CPROVER_get_field(z + 3, "field1") == 13);
  assert(__CPROVER_get_field(z + 3, "field2") == 14);
  assert(__CPROVER_get_field(z + 4, "field1") == 15);
  assert(__CPROVER_get_field(z + 4, "field2") == 16);

  int l;
  __CPROVER_assume(0 <= l && l < n);
  __CPROVER_set_field(&(C[l]), "field1", 42);
  assert(__CPROVER_get_field(&(C[l]), "field1") == 42);

  z = &(C[l]);
  __CPROVER_set_field(z, "field1", 43);
  assert(__CPROVER_get_field(z, "field1") == 43);
}
