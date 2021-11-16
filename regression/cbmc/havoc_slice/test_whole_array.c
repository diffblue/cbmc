#include "declarations.h"

void main(void)
{
  // INITIALIZE
  int a[5] = {0, 1, 2, 3, 4};
  int old_a[5] = {0, 1, 2, 3, 4};

  // HAVOC WHOLE ARRAY
  __CPROVER_havoc_slice(a, __CPROVER_OBJECT_SIZE(a));

  // POSTCONDITIONS
  __CPROVER_assert(a[0] == old_a[0], "expecting FAILURE");
  __CPROVER_assert(a[1] == old_a[1], "expecting FAILURE");
  __CPROVER_assert(a[2] == old_a[2], "expecting FAILURE");
  __CPROVER_assert(a[3] == old_a[3], "expecting FAILURE");
  __CPROVER_assert(a[4] == old_a[4], "expecting FAILURE");

  return;
}
