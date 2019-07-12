#include <stdlib.h>

int main()
{
  int a = 42;
  size_t mask = ~(size_t)0;
  // applying bitmasks to pointers is used to defend against speculative
  // execution side channels, hence we need to support this
  __CPROVER_assert(*(int *)(mask & (size_t)&a) == 42, "");

  // the following bitmasks are for completeness of the test only, they aren't
  // necessarily as useful in practice
  size_t mask_zero = 0;
  __CPROVER_assert(*(int *)(mask_zero | (size_t)&a) == 42, "");
  __CPROVER_assert(*(int *)(mask_zero ^ (size_t)&a) == 42, "");
}
