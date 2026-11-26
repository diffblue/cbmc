#include <assert.h>

struct S
{
  int *p;
  char c;
};

union U
{
  int *p;
  long l;
};

int main()
{
  __CPROVER_field_decl_local("tag", (unsigned char)0);
  struct S s;
  union U u;
  int *arr[2];

  __CPROVER_set_field(&s.p, "tag", (unsigned char)0x81);
  __CPROVER_set_field(&u, "tag", (unsigned char)5);
  __CPROVER_set_field(&arr[1], "tag", (unsigned char)7);

  assert(__CPROVER_get_field(&s.p, "tag") == 0x81);
  assert(__CPROVER_get_field(&u.p, "tag") == 5);
  assert(__CPROVER_get_field(&arr[1], "tag") == 7);
}
