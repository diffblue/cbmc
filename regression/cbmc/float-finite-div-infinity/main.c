// Test case for bug fix: finite / +INFINITY should NOT trigger --nan-check
// According to IEEE 754-2019 Section 6.1: "division(x, ∞) for finite x"
// should produce 0.0, not NaN. Hence, none of the operations below should
// trigger nan-check assertions.

#include <assert.h>
#include <math.h>
#include <stdint.h>

union float_bits
{
  uint32_t u;
  float f;
};

int main(void)
{
  // Test case 1: Using union to create +INFINITY as mentioned in the bug report
  union float_bits a, b;
  a.u = 1065353216; // 1.0
  b.u = 2139095040; // +INF

  // This should produce 0.0, not NaN - should NOT trigger nan-check failure
  float result1 = a.f / b.f;
  assert(fpclassify(result1) == FP_ZERO && !signbit(result1));

  // Test case 2: Direct assignment as mentioned in the bug report
  float x = 1.0f;
  float y = INFINITY;
  float result2 = x / y;
  assert(fpclassify(result2) == FP_ZERO && !signbit(result2));

  // Test case 3: Negative finite / infinity should also be 0.0 (negative zero)
  float neg_x = -1.0f;
  float result3 = neg_x / INFINITY;
  assert(fpclassify(result3) == FP_ZERO && signbit(result3));

  // Test case 4: Various finite values divided by infinity
  float nd_positive = __VERIFIER_nondet_float();
  __CPROVER_assume(isfinite(nd_positive) && nd_positive > 0);
  float result4 = nd_positive / INFINITY;
  assert(fpclassify(result4) == FP_ZERO && !signbit(result4));
  float nd_negative = __VERIFIER_nondet_float();
  __CPROVER_assume(isfinite(nd_negative) && nd_negative < 0);
  float result5 = nd_negative / INFINITY;
  assert(fpclassify(result5) == FP_ZERO && signbit(result5));

  return 0;
}
