// IEEE 754 remainder tie-breaking: remainderf(3.0, 2.0) == -1.0
// The nearest even quotient is 2, so remainder = 3 - 2*2 = -1.

#include <assert.h>
#include <math.h>

int main()
{
  float r = remainderf(3.0f, 2.0f);
  assert(r == -1.0f);

  return 0;
}
