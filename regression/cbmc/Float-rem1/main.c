// Based on Z3#2381: IEEE 754 remainder.
// CBMC crashes with invariant violation on remainderf/remainder.
// This is a known bug in CBMC's handling of the remainder function.

#include <assert.h>
#include <math.h>

int main()
{
  float r = remainderf(3.0f, 2.0f);
  assert(r == -1.0f);

  return 0;
}
