#include <assert.h>
#include <stdlib.h>

struct STRUCTNAME
{
  int x1;
  int B1[3];
};

void f_void_ptr(void *s)
{
  assert(__CPROVER_get_field(s, "field1") == 0);
}

int main()
{
  __CPROVER_field_decl_local("field1", (char)0);

  struct STRUCTNAME z;
  f_void_ptr(&z);
}
