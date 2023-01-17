#include <assert.h>
#include <stdlib.h>

struct STRUCTNAME
{
  int data;
  struct STRUCTNAME *next;
};

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);

  struct STRUCTNAME a;

  assert(__CPROVER_get_field(&a, "field1") == 0);
  assert(__CPROVER_get_field(&(a.data), "field1") == 0);
  assert(__CPROVER_get_field(&(a.next), "field1") == 0);
  // Expect a warning here. We return 0 as default value.
  assert(__CPROVER_get_field(a.next, "field1") == 0);
  // Expect a warning here. We return 0 as default value.
  assert(__CPROVER_get_field((*(a.next)).next, "field1") == 0);

  __CPROVER_set_field(&(a.data), "field1", 1);
  __CPROVER_set_field(&(a.next), "field1", 1);
  // Expect a warning here. We cannot set SM because it doesn't exist.
  __CPROVER_set_field(&((*(a.next)).data), "field1", 1);
  // Expect a warning here. We cannot set SM because it doesn't exist.
  __CPROVER_set_field(&((*(*(a.next)).next).data), "field1", 1);

  assert(__CPROVER_get_field(&a, "field1") == 1);
  assert(__CPROVER_get_field(&(a.data), "field1") == 1);
  assert(__CPROVER_get_field(&(a.next), "field1") == 1);
  // Expect a warning here. We return 0 as default value.
  assert(__CPROVER_get_field(a.next, "field1") == 0);
  // Expect a warning here. We return 0 as default value.
  assert(__CPROVER_get_field((*(a.next)).next, "field1") == 0);

  struct STRUCTNAME b;
  a.next = &b;

  assert(__CPROVER_get_field(&a, "field1") == 1);
  assert(__CPROVER_get_field(&(a.data), "field1") == 1);
  assert(__CPROVER_get_field(&(a.next), "field1") == 1);
  // No warning here.
  assert(__CPROVER_get_field(a.next, "field1") == 0);
  // Expect a warning here. We return 0 as default value.
  assert(__CPROVER_get_field((*(a.next)).next, "field1") == 0);

  // No warning here.
  __CPROVER_set_field(&((*(a.next)).data), "field1", 1);
  // Expect a warning here. We cannot set SM because it doesn't exist.
  __CPROVER_set_field(&((*(*(a.next)).next).data), "field1", 1);

  // No warning here.
  assert(__CPROVER_get_field(a.next, "field1") == 1);
  // Expect a warning here. We return 0 as default value.
  assert(__CPROVER_get_field((*(a.next)).next, "field1") == 0);

  struct STRUCTNAME c;
  b.next = &c;
  // No warning here.
  assert(__CPROVER_get_field((*(a.next)).next, "field1") == 0);

  // No warning here.
  __CPROVER_set_field(&((*(*(a.next)).next).data), "field1", 1);

  // No warning here.
  assert(__CPROVER_get_field((*(a.next)).next, "field1") == 1);
}
