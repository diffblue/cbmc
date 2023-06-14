#include <assert.h>

enum E
{
  V0 = 0,
  V1 = 1,
  V2 = 2
};

int main()
{
  enum E e;
  e = V1;
  __CPROVER_assume(__CPROVER_enum_is_in_range(e));
  __CPROVER_assert(e > 10, "Variable e is V1, so this should fail");
}
