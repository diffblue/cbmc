#include <assert.h>
#include <stdlib.h>

struct STRUCTNAME
{
  int data;
  struct STRUCTNAME *next;
};

int main()
{
  int x;
  int y;
  __CPROVER_assume(x > 0);
  __CPROVER_assume(y > x);

  // This is always != 0, but symex doesn't know that.
  // So, we force it to produce a case split on shadow memory access.
  int choice = y / x;

  __CPROVER_field_decl_local("field1", (_Bool)0);

  struct STRUCTNAME a;
  a.next = (struct STRUCTNAME *)0;

  assert(__CPROVER_get_field(&a, "field1") == 0);
  assert(__CPROVER_get_field(&(a.data), "field1") == 0);
  assert(__CPROVER_get_field(&(a.next), "field1") == 0);

  __CPROVER_set_field(&(a.data), "field1", 1);
  __CPROVER_set_field(&(a.next), "field1", 1);

  assert(__CPROVER_get_field(&a, "field1") == 1);
  assert(__CPROVER_get_field(&(a.data), "field1") == 1);
  assert(__CPROVER_get_field(&(a.next), "field1") == 1);

  struct STRUCTNAME b;
  b.next = (struct STRUCTNAME *)0;
  if(choice)
  {
    a.next = &b;
  }

  assert(__CPROVER_get_field(&a, "field1") == 1);
  assert(__CPROVER_get_field(&(a.data), "field1") == 1);
  assert(__CPROVER_get_field(&(a.next), "field1") == 1);
  // No warning here.
  assert(__CPROVER_get_field(a.next, "field1") == 0);

  // No warning here.
  __CPROVER_set_field(&((*(a.next)).data), "field1", 1);

  // No warning here.
  assert(__CPROVER_get_field(a.next, "field1") == 1);

  struct STRUCTNAME c;
  c.next = (struct STRUCTNAME *)0;
  if(choice)
  {
    b.next = &c;
  }

  // No warning here.
  assert(__CPROVER_get_field((*(a.next)).next, "field1") == 0);

  // No warning here.
  __CPROVER_set_field(&((*(*(a.next)).next).data), "field1", 1);

  // No warning here.
  assert(__CPROVER_get_field((*(a.next)).next, "field1") == 1);
}
