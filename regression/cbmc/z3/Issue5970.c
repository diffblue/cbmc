#include <assert.h>

void main()
{
  unsigned A, x[64];
  // clang-format off
  __CPROVER_assume(0 <= A && A < 64);
  __CPROVER_assume(__CPROVER_forall { int i ; (0 <= i && i < A) ==> x[i] >= 1 });
  // clang-format on
  assert(x[0] > 0);
}
