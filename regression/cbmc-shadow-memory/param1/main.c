#include <assert.h>
#include <stdlib.h>

struct STRUCTNAME
{
  int x1;
  int B1[3];
};

void f_int_val(int x)
{
  // x has its own shadow memory
  assert(__CPROVER_get_field(&x, "field1") == 0);
  __CPROVER_set_field(&x, "field1", 1);
  assert(__CPROVER_get_field(&x, "field1") == 1);
}

void f_intptr_ptr0(int *x)
{
  // we access the argument's shadow memory
  assert(__CPROVER_get_field(x, "field1") == 255);
  __CPROVER_set_field(x, "field1", 1);
  assert(__CPROVER_get_field(x, "field1") == 1);
}

void f_intptr_ptr1(int *x)
{
  // we access the argument's shadow memory
  assert(__CPROVER_get_field(x, "field1") == 1);
  __CPROVER_set_field(x, "field1", 2);
  assert(__CPROVER_get_field(x, "field1") == 2);
}

void f_intptr_val(int *x)
{
  // x has its own shadow memory
  assert(__CPROVER_get_field(&x, "field1") == 0);
  __CPROVER_set_field(&x, "field1", 3);
  assert(__CPROVER_get_field(&x, "field1") == 3);
}

void f_intarray_ptr0(int x[])
{
  // we access the argument's shadow memory
  assert(__CPROVER_get_field(&(x[0]), "field1") == 255);
  __CPROVER_set_field(&(x[0]), "field1", 1);
  assert(__CPROVER_get_field(&(x[0]), "field1") == 1);
}

void f_intarray_ptr1(int x[])
{
  // we access the argument's shadow memory
  assert(__CPROVER_get_field(&(x[0]), "field1") == 1);
  __CPROVER_set_field(&(x[0]), "field1", 2);
  assert(__CPROVER_get_field(&(x[0]), "field1") == 2);
}

void f_struct_val(struct STRUCTNAME x)
{
  // x has its own shadow memory
  assert(__CPROVER_get_field(&(x.B1[2]), "field1") == 0);
  __CPROVER_set_field(&(x.B1[2]), "field1", 5);
  assert(__CPROVER_get_field(&(x.B1[2]), "field1") == 5);
}

void f_structptr_ptr0(struct STRUCTNAME *x)
{
  // we access the argument's shadow memory
  assert(__CPROVER_get_field(&(x->B1[2]), "field1") == 255);
  __CPROVER_set_field(&(x->B1[2]), "field1", 1);
  assert(__CPROVER_get_field(&(x->B1[2]), "field1") == 1);
}

void f_structptr_ptr1(struct STRUCTNAME *x)
{
  // we access the argument's shadow memory
  assert(__CPROVER_get_field(&(x->B1[2]), "field1") == 1);
  __CPROVER_set_field(&(x->B1[2]), "field1", 2);
  assert(__CPROVER_get_field(&(x->B1[2]), "field1") == 2);
}

void f_structptr_val(struct STRUCTNAME *x)
{
  // x has its own shadow memory
  assert(__CPROVER_get_field(&x, "field1") == 0);
  __CPROVER_set_field(&x, "field1", 7);
  assert(__CPROVER_get_field(&x, "field1") == 7);
}

void f_int_local(int rec, int value)
{
  // locals in each recursive call instance have their own shadow memory
  int x;
  assert(__CPROVER_get_field(&x, "field1") == 0);
  __CPROVER_set_field(&x, "field1", value);
  assert(__CPROVER_get_field(&x, "field1") == value);
  if(rec)
  {
    f_int_local(0, value + 1);
    assert(__CPROVER_get_field(&x, "field1") == value);
  }
}

int main()
{
  __CPROVER_field_decl_local("field1", (char)0);
  int x;
  __CPROVER_set_field(&x, "field1", 255);
  f_int_val(x);
  f_int_val(x);
  f_intptr_ptr0(&x);
  f_intptr_ptr1(&x);
  f_intptr_val(&x);
  f_intptr_val(&x);
  int y[1];
  __CPROVER_set_field(&y[0], "field1", 255);
  f_intarray_ptr0(y);
  f_intarray_ptr1(y);
  struct STRUCTNAME z;
  __CPROVER_set_field(&z, "field1", 255);
  f_struct_val(z);
  f_struct_val(z);
  f_structptr_ptr0(&z);
  f_structptr_ptr1(&z);
  f_structptr_val(&z);
  f_structptr_val(&z);
  f_int_local(1, 1);
}
