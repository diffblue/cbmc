#include <assert.h>

int nondet_int();

int main()
{
  __CPROVER_field_decl_local("tag", (unsigned char)0);
  int x;
  int *p = &x;
  __CPROVER_set_field(&p, "tag", (unsigned char)3);
  unsigned char tag = __CPROVER_get_field(&p, "tag");
  int sum = 0;
  if(tag != 3)
  {
    // never executed, but symex explores it unless it knows tag == 3
    for(int i = 0; i < 100; ++i)
      sum += nondet_int();
  }
  assert(tag == 3);
}
