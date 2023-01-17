#include <assert.h>
#include <stdlib.h>

struct STRUCTNAME
{
  int x;
};

void f_charptr_val(char *__cs_param)
{
  // Access to shadow memory of z.
  assert(__CPROVER_get_field(__cs_param, "field1") == 255);

  // Fails because parameter itself doesn't have shadow memory.
  assert(__CPROVER_get_field(&__cs_param, "field1") == 0);
}

int main()
{
  __CPROVER_field_decl_local("field1", (char)0);

  char *__cs_threadargs[2];
  struct STRUCTNAME z;
  __CPROVER_set_field(&z, "field1", 255);

  __cs_threadargs[1] = (char *)(&z);
  f_charptr_val(__cs_threadargs[1]);
}
