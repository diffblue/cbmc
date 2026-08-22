// Test that FMA correctly computes the sign of infinity and zero results.
//
// Bug: float_bvt::fma always used the add/sub sign as the result sign,
// ignoring the special-case rules for infinity and zero. As a result:
//   - For infinity results, the sign could be wrong when the product is
//     infinite but the addend is finite (or vice versa), because the
//     product sign and addend sign differ.
//   - For exact-zero results (cancellation), the signed-zero conventions
//     for the rounding mode were not respected. In particular, under
//     round-to-minus-inf (FE_DOWNWARD), +0 + (-0) must yield -0, but the
//     pre-fix code could produce +0.
//
// All cases below call plain `fmaf` (not `__CPROVER_fmaf`) so that the
// library wrapper is exercised too: with the tightened wrapper that
// only raises FE_INVALID for actual inf - inf, none of these inputs
// trigger a spurious exception.  This also gives the test free
// coverage of the wrapper's flag handling per IEEE-754.

#include <assert.h>
#include <math.h>

#ifndef _MSC_VER
#  include <fenv.h>
#endif

extern int __CPROVER_rounding_mode;

// Force an exact-zero FMA result by exact cancellation between the
// product and the addend, then check the resulting signbit.
void testFmaZero(int mode, float x, float y, float z, int expected_sign)
{
#ifndef _MSC_VER
  int error = fesetround(mode);
  assert(error == 0);

  float r = fmaf(x, y, z);
  assert(r == 0.0f);
  assert(signbit(r) == expected_sign);
#endif

  return;
}

int main()
{
  float a, b, c;

  // Test 1: (+inf) * (+2) + 42 = +inf (sign from product)
  __CPROVER_assume(isinf(a) && a > 0);
  __CPROVER_assume(b == 2.0f);
  __CPROVER_assume(c == 42.0f);

  __CPROVER_rounding_mode = 0;
  float r1 = fmaf(a, b, c);
  assert(isinf(r1) && r1 > 0);

  // Test 2: (+inf) * (-3) + 100 = -inf (sign from product)
  float d, e, f;
  __CPROVER_assume(isinf(d) && d > 0);
  __CPROVER_assume(e == -3.0f);
  __CPROVER_assume(f == 100.0f);

  __CPROVER_rounding_mode = 0;
  float r2 = fmaf(d, e, f);
  assert(isinf(r2) && r2 < 0);

  // Test 3: 2 * 3 + (+inf) = +inf (sign from addend)
  float g, h, i;
  __CPROVER_assume(g == 2.0f);
  __CPROVER_assume(h == 3.0f);
  __CPROVER_assume(isinf(i) && i > 0);

  __CPROVER_rounding_mode = 0;
  float r3 = fmaf(g, h, i);
  assert(isinf(r3) && r3 > 0);

  // Test 4: 2 * 3 + (-inf) = -inf (sign from addend)
  float j, k, l;
  __CPROVER_assume(j == 2.0f);
  __CPROVER_assume(k == 3.0f);
  __CPROVER_assume(isinf(l) && l < 0);

  __CPROVER_rounding_mode = 0;
  float r4 = fmaf(j, k, l);
  assert(isinf(r4) && r4 < 0);

#ifndef _MSC_VER
  // Zero-result sign tests, exercising the new zero_sign computation in
  // float_bvt::fma (the OR-of-signs term under FE_DOWNWARD vs the
  // AND-of-signs term in other modes).

  // Exact cancellation: 1 * 1 + (-1) = 0
  // FE_TONEAREST yields +0 (AND of signs: +,- -> +).
  testFmaZero(FE_TONEAREST, 1.0f, 1.0f, -1.0f, 0);
  // FE_DOWNWARD yields -0 (OR of signs: +,- -> -).
  testFmaZero(FE_DOWNWARD, 1.0f, 1.0f, -1.0f, 1);

  // Exact cancellation with negated product: (-1) * 1 + 1 = 0
  // FE_TONEAREST yields +0 (AND of signs: -,+ -> +).
  testFmaZero(FE_TONEAREST, -1.0f, 1.0f, 1.0f, 0);
  // FE_DOWNWARD yields -0 (OR of signs: -,+ -> -).
  testFmaZero(FE_DOWNWARD, -1.0f, 1.0f, 1.0f, 1);

  // Both contributing signs negative: (-0) * 1 + (-0) = -0
  // The product's sign is the XOR of the factor signs, so (-0) * 1 has
  // sign -, and addend has sign -; AND yields -, OR yields -.
  testFmaZero(FE_TONEAREST, -0.0f, 1.0f, -0.0f, 1);
  testFmaZero(FE_DOWNWARD, -0.0f, 1.0f, -0.0f, 1);

  // Both contributing signs positive: 0 * 1 + 0 = +0 in every mode.
  testFmaZero(FE_TONEAREST, 0.0f, 1.0f, 0.0f, 0);
  testFmaZero(FE_DOWNWARD, 0.0f, 1.0f, 0.0f, 0);

  // Mixed: (+0) * 1 + (-0) = +0 under FE_TONEAREST, -0 under FE_DOWNWARD.
  testFmaZero(FE_TONEAREST, 0.0f, 1.0f, -0.0f, 0);
  testFmaZero(FE_DOWNWARD, 0.0f, 1.0f, -0.0f, 1);
#endif

  return 0;
}
