#include <assert.h>

int main()
{
  __CPROVER_field_decl_local("field1", (_Bool)0);

  int x;

  // create a non-trivial counterexample trace
  for(int i = 0; i < 4; ++i)
  {
    if(i == 2)
    {
      __CPROVER_set_field(&x, "field1", 1);
    }
  }

  assert(__CPROVER_get_field(&x, "field1") == 0);
}
