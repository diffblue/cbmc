// Test that ROUND_TO_AWAY (rounding mode 4) correctly rounds to the
// nearest representable value, only rounding away from zero on exact ties.
//
// Bug: float_bvt was rounding away from zero even for non-tie cases.
//
// The test uses non-deterministic inputs constrained to specific values
// to force the solver to exercise the float encoding.

#include <assert.h>

int main()
{
  // --- Test 1: non-tie addition under ROUND_TO_AWAY ---
  // a + b is very close to -1.0 but not a tie.
  // The nearest float is 0xBF7FFFFF (-0x1.fffffep-1), not -1.0 (0xBF800000).
  // ROUND_TO_AWAY must still pick the nearest value.
  float a, b;
  __CPROVER_assume(a == -0.9961287975311279f);    // 0xBF7F024C
  __CPROVER_assume(b == -0.0038711430970579386f); // 0xBB7DB301

  __CPROVER_rounding_mode = 4;
  float sum = a + b;
  // The exact sum is ~-0.999999940628..., closer to -0x1.fffffep-1 than -1.0;
  // the buggy formula would round away to -1.0f.
  assert(sum == -0x1.fffffep-1f);

  // --- Test 2: tie addition under ROUND_TO_AWAY ---
  // 1.0f + 2^-24 = 0x1.000001p+0 (exact tie).
  // ROUND_TO_AWAY rounds away from zero -> 0x1.000002p+0f.
  float c, d;
  __CPROVER_assume(c == 1.0f);
  __CPROVER_assume(d == 0x1.0p-24f);

  __CPROVER_rounding_mode = 4;
  float tie_sum = c + d;
  assert(tie_sum == 0x1.000002p+0f);

  // --- Test 3: non-tie multiplication under ROUND_TO_AWAY ---
  // In real arithmetic 1.5 * 1.1 = 1.65, but 1.1f is not exactly representable
  // in binary32, so the operands are already rounded. The product is not a
  // tie, so ROUND_TO_AWAY rounds to nearest, the same as ROUND_TO_EVEN:
  // 1.5f * 1.1f = 0x1.a66668p+0f (1.65000009...).
  float e, f;
  __CPROVER_assume(e == 1.5f);
  __CPROVER_assume(f == 1.1f);

  __CPROVER_rounding_mode = 4;
  float prod = e * f;
  assert(prod == 0x1.a66668p+0f);

  return 0;
}
