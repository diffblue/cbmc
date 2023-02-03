#include <assert.h>
#include <stdlib.h>

struct STRUCTNAME
{
  int x1;
  int B1[3];
};

void f_void_ptr_cast(void *s)
{
  assert(__CPROVER_get_field((struct STRUCTNAME *)s, "field1") == 0);
  __CPROVER_set_field(&((struct STRUCTNAME *)s)->x1, "field1", 1);
  assert(__CPROVER_get_field((struct STRUCTNAME *)s, "field1") == 1);
}

int main()
{
  __CPROVER_field_decl_local("field1", (char)0);

  struct STRUCTNAME z;
  f_void_ptr_cast(&z);
}
