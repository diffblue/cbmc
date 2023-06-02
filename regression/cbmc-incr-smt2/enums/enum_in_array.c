#include <assert.h>

enum E
{
  V0 = 0,
  V1 = 1,
  V2 = 2
};

int main()
{
  unsigned i;
  __CPROVER_assume(i < 3);
  enum E e[3];
  e[0] = V0;
  e[1] = V1;
  e[2] = V2;
  __CPROVER_assert(e[i] > 0, "Array at index 0 is V0, so this should fail");
}
