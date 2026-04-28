// Test that FMA correctly computes the sign of infinity results.
//
// Bug: float_bvt did not handle the sign of infinity results in FMA,
// always using the add/sub sign instead.
//
// Uses __CPROVER_fmaf directly to bypass the library wrapper's
// exception-raising assertions.

#include <assert.h>
#include <math.h>

extern int __CPROVER_rounding_mode;
float __CPROVER_fmaf(float, float, float);

int main()
{
  float a, b, c;

  // Test 1: (+inf) * (+2) + 42 = +inf (sign from product)
  __CPROVER_assume(isinf(a) && a > 0);
  __CPROVER_assume(b == 2.0f);
  __CPROVER_assume(c == 42.0f);

  __CPROVER_rounding_mode = 0;
  float r1 = __CPROVER_fmaf(a, b, c);
  assert(isinf(r1) && r1 > 0);

  // Test 2: (+inf) * (-3) + 100 = -inf (sign from product)
  float d, e, f;
  __CPROVER_assume(isinf(d) && d > 0);
  __CPROVER_assume(e == -3.0f);
  __CPROVER_assume(f == 100.0f);

  __CPROVER_rounding_mode = 0;
  float r2 = __CPROVER_fmaf(d, e, f);
  assert(isinf(r2) && r2 < 0);

  // Test 3: 2 * 3 + (+inf) = +inf (sign from addend)
  float g, h, i;
  __CPROVER_assume(g == 2.0f);
  __CPROVER_assume(h == 3.0f);
  __CPROVER_assume(isinf(i) && i > 0);

  __CPROVER_rounding_mode = 0;
  float r3 = __CPROVER_fmaf(g, h, i);
  assert(isinf(r3) && r3 > 0);

  // Test 4: 2 * 3 + (-inf) = -inf (sign from addend)
  float j, k, l;
  __CPROVER_assume(j == 2.0f);
  __CPROVER_assume(k == 3.0f);
  __CPROVER_assume(isinf(l) && l < 0);

  __CPROVER_rounding_mode = 0;
  float r4 = __CPROVER_fmaf(j, k, l);
  assert(isinf(r4) && r4 < 0);

  return 0;
}
