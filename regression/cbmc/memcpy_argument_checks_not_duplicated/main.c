#include <string.h>

int main()
{
  char dst[4], src[4];
  unsigned i;
  __CPROVER_assume(i < 4);
  // the checks of `src + i' are made once per use, not again for the
  // instantiated memcpy preconditions
  memcpy(dst, src + i, 1);
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
