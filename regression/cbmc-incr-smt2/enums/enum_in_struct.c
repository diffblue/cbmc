#include <assert.h>

enum E
{
  V0 = 0,
  V1 = 1,
  V2 = 2
};

struct S
{
  enum E a;
  int b;
};

int main()
{
  struct S s;
  s.a = V1;
  __CPROVER_assume(__CPROVER_enum_is_in_range(s.a));
  __CPROVER_assert(s.a > 10, "Struct field s.a is V1, so this should fail");
}
