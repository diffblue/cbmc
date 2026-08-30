// Test that round-to-integral (rintf, rint) works correctly under various
// rounding modes, special-value inputs, denormals, and at the boundaries
// where the f-deep ITE cascade dispatches.
//
// Without the rewrite, `cbmc --smt2 --z3` (the non-FPA SMT path, exercised
// by test_smt.desc) hits an UNEXPECTEDCASE invariant in
// smt2_conv.cpp::convert_floatbv_round_to_integral, so this regression
// pins down the user-visible fix on that path.

#include <assert.h>
#include <float.h>
#include <math.h>

extern int __CPROVER_rounding_mode;

int main()
{
  // Rounding-mode encoding (matches ieee_floatt::rounding_modet):
  //   0 = ROUND_TO_EVEN
  //   1 = ROUND_TO_MINUS_INF
  //   2 = ROUND_TO_PLUS_INF
  //   3 = ROUND_TO_ZERO
  //   4 = ROUND_TO_AWAY

  // ROUND_TO_EVEN: ties round to even.
  __CPROVER_rounding_mode = 0;
  float a = 2.5f;
  float r1 = rintf(a);
  assert(r1 == 2.0f);

  __CPROVER_rounding_mode = 0;
  float b = 3.5f;
  float r2 = rintf(b);
  assert(r2 == 4.0f);

  // Negative ties under ROUND_TO_EVEN.
  __CPROVER_rounding_mode = 0;
  float bn1 = -2.5f;
  float rn1 = rintf(bn1);
  assert(rn1 == -2.0f);

  __CPROVER_rounding_mode = 0;
  float bn2 = -3.5f;
  float rn2 = rintf(bn2);
  assert(rn2 == -4.0f);

  // ROUND_TO_PLUS_INF (ceil).
  __CPROVER_rounding_mode = 2;
  float c = 2.3f;
  float r3 = rintf(c);
  assert(r3 == 3.0f);

  // ROUND_TO_MINUS_INF (floor).
  __CPROVER_rounding_mode = 1;
  float d = 2.7f;
  float r4 = rintf(d);
  assert(r4 == 2.0f);

  // ROUND_TO_ZERO (truncate).
  __CPROVER_rounding_mode = 3;
  float e = -2.7f;
  float r5 = rintf(e);
  assert(r5 == -2.0f);

  // ROUND_TO_AWAY: 0.5 rounds away from zero.
  __CPROVER_rounding_mode = 4;
  float aw1 = 0.5f;
  float r_aw1 = rintf(aw1);
  assert(r_aw1 == 1.0f);

  __CPROVER_rounding_mode = 4;
  float aw2 = -0.5f;
  float r_aw2 = rintf(aw2);
  assert(r_aw2 == -1.0f);

  __CPROVER_rounding_mode = 4;
  float aw3 = 2.5f;
  float r_aw3 = rintf(aw3);
  assert(r_aw3 == 3.0f);

  // Already-integral input (small).
  __CPROVER_rounding_mode = 0;
  float f = 42.0f;
  float r6 = rintf(f);
  assert(r6 == 42.0f);

  // Already-integral input with unbiased exponent >= f for float (f=23):
  // 2^24 = 16777216 has biased exp 1023+24 = 1047, well past the loop
  // upper bound. Exercises the exp_ge_f early-out.
  __CPROVER_rounding_mode = 0;
  float big_int = 16777216.0f;
  float r_big = rintf(big_int);
  assert(r_big == 16777216.0f);

  // Special values: should pass through unchanged via is_special.
  // NaN.
  __CPROVER_rounding_mode = 0;
  float nan_in;
  __CPROVER_assume(isnan(nan_in));
  float r_nan = rintf(nan_in);
  assert(isnan(r_nan));

  // +Infinity.
  __CPROVER_rounding_mode = 0;
  float inf_pos;
  __CPROVER_assume(inf_pos == INFINITY);
  float r_ip = rintf(inf_pos);
  assert(isinf(r_ip) && r_ip > 0);

  // -Infinity.
  __CPROVER_rounding_mode = 0;
  float inf_neg;
  __CPROVER_assume(inf_neg == -INFINITY);
  float r_in = rintf(inf_neg);
  assert(isinf(r_in) && r_in < 0);

  // +0.0.
  __CPROVER_rounding_mode = 0;
  float pz = 0.0f;
  float r_pz = rintf(pz);
  assert(r_pz == 0.0f);

  // -0.0 should preserve sign under any mode.
  __CPROVER_rounding_mode = 0;
  float nz = -0.0f;
  float r_nz = rintf(nz);
  assert(r_nz == 0.0f); // both ±0 compare equal to 0
  assert(signbit(r_nz));

  // Denormals: rintf of a positive denormal under ROUND_TO_EVEN -> +0.
  __CPROVER_rounding_mode = 0;
  float den = FLT_MIN / 2.0f;
  float r_den = rintf(den);
  assert(r_den == 0.0f);

  // Denormal under ROUND_TO_PLUS_INF (ceil) -> +1.
  __CPROVER_rounding_mode = 2;
  float den2 = FLT_MIN / 2.0f;
  float r_den2 = rintf(den2);
  assert(r_den2 == 1.0f);

  // double / rint coverage. Exercises a different fraction width (f=52).
  __CPROVER_rounding_mode = 0;
  double da = 2.5;
  double dr1 = rint(da);
  assert(dr1 == 2.0);

  __CPROVER_rounding_mode = 0;
  double db = 3.5;
  double dr2 = rint(db);
  assert(dr2 == 4.0);

  __CPROVER_rounding_mode = 1;
  double dc = -2.7;
  double dr3 = rint(dc);
  assert(dr3 == -3.0);

  // double already-integral past the loop bound (2^53 = 9007199254740992).
  __CPROVER_rounding_mode = 0;
  double dbig = 9007199254740992.0;
  double dr_big = rint(dbig);
  assert(dr_big == 9007199254740992.0);

  return 0;
}
