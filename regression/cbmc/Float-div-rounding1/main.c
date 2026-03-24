// Based on CVC5#11139 and Bitwuzla#130: Division with various inputs.
// Test that CBMC correctly handles float division, including edge cases.

#include <assert.h>
#include <math.h>

int main()
{
  float a, b;

  // Division by zero produces infinity
  __CPROVER_assume(a == 1.0f);
  __CPROVER_assume(b == 0.0f);
  float r1 = a / b;
  assert(isinf(r1));

  // 0 / nonzero = 0
  float c = 0.0f;
  float d;
  __CPROVER_assume(d == 2.0f);
  float r2 = c / d;
  assert(r2 == 0.0f);

  // NaN / anything = NaN
  float r3 = NAN / 1.0f;
  assert(isnan(r3));

  return 0;
}
