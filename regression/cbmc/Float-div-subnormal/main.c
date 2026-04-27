// Test division with subnormal dividend.
//
// Bug: float_utilst and float_bvt had insufficient division width,
// causing 1-ULP errors when the dividend is subnormal (leading zeros
// in the fraction reduce the effective precision of the quotient).

#include <assert.h>
#include <float.h>
#include <math.h>

int main()
{
  // A subnormal divided by a normal.
  // FLT_MIN / 2 is the smallest normal; values below are subnormal.
  float a, b;
  __CPROVER_assume(a == FLT_MIN * 0.5f); // subnormal
  __CPROVER_assume(b == 2.0f);

  float r = a / b;
  // The result should be exactly FLT_MIN * 0.25, also subnormal.
  assert(r == FLT_MIN * 0.25f);

  // Another case: subnormal / large normal
  float c, d;
  __CPROVER_assume(c == FLT_MIN * 0.75f);
  __CPROVER_assume(d == 3.0f);

  float r2 = c / d;
  assert(r2 == FLT_MIN * 0.25f);

  return 0;
}
