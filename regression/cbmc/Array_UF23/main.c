/// \file
/// Test that Ackermann constraints are reduced by the weak equivalence
/// optimisation: derived arrays (with, if, etc.) do not need Ackermann
/// constraints because they are implied by the with/if constraints plus
/// Ackermann on base arrays.
#include <stdlib.h>
int main()
{
  size_t array_size;
  int a[array_size];
  int i0, i1, i2, i3, i4;

  a[i0] = 0;
  a[i1] = 1;
  a[i2] = 2;
  a[i3] = 3;
  a[i4] = 4;

  __CPROVER_assert(a[i0] >= 0, "a[i0] >= 0");
  return 0;
}
