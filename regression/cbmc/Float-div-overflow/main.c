// Test that division overflow is handled correctly under all rounding
// modes, in both the bitvector and SMT encodings.
//
// Bug 1 (float_bvt::div): the exponent was extended by only 1 bit
// instead of 2, leaving the post-`+spec.f` adjustment vulnerable to
// silent wraparound on large quotients. The FLT_MAX / FLT_MIN
// (single) and DBL_MAX / DBL_MIN (double) cases below exercise the
// extended exponent path. (Empirically these inputs already saturate
// to the correct ±inf via downstream denormalization handling on
// both pre-fix and post-fix encoders, so they don't fail on develop;
// they are still kept here as exercise of the corrected path.)
//
// Bug 2 (round_exponent in both encoders): overflow_to_inf did not
// include ROUND_TO_AWAY. Since ROUND_TO_AWAY is a round-to-nearest
// mode, overflow must produce ±inf. The ROUND_TO_AWAY cases below
// pin that fix down — reverting the round_to_away disjunct in either
// encoder leaves the test green if those cases are absent.

#include <assert.h>
#include <float.h>
#include <math.h>

// Rounding-mode encoding mirrors src/util/ieee_float.h
// (and matches the x86 control-word values).
#define ROUND_TO_EVEN 0
#define ROUND_TO_MINUS_INF 1
#define ROUND_TO_PLUS_INF 2
#define ROUND_TO_ZERO 3
#define ROUND_TO_AWAY 4

extern int __CPROVER_rounding_mode;

int main()
{
  float a, b;
  __CPROVER_assume(a == FLT_MAX);
  __CPROVER_assume(b == 0.5f);

  // ---- bug 2 coverage (overflow under each rounding mode) ----

  // ROUND_TO_EVEN: positive overflow -> +inf
  __CPROVER_rounding_mode = ROUND_TO_EVEN;
  float r0 = a / b;
  assert(isinf(r0) && r0 > 0);

  // ROUND_TO_ZERO: directed toward zero -> FLT_MAX
  __CPROVER_rounding_mode = ROUND_TO_ZERO;
  float r3 = a / b;
  assert(r3 == FLT_MAX);

  // ROUND_TO_PLUS_INF: directed toward +inf -> +inf
  __CPROVER_rounding_mode = ROUND_TO_PLUS_INF;
  float r2 = a / b;
  assert(isinf(r2) && r2 > 0);

  // ROUND_TO_MINUS_INF: directed toward -inf -> FLT_MAX
  __CPROVER_rounding_mode = ROUND_TO_MINUS_INF;
  float r1 = a / b;
  assert(r1 == FLT_MAX);

  // ROUND_TO_AWAY: round-to-nearest, ties away from zero -> +inf.
  // This case directly exercises the round_to_away disjunct in
  // round_exponent's overflow_to_inf.
  __CPROVER_rounding_mode = ROUND_TO_AWAY;
  float r4 = a / b;
  assert(isinf(r4) && r4 > 0);

  // Negative overflow: -FLT_MAX / 0.5f
  float c;
  __CPROVER_assume(c == -FLT_MAX);

  // ROUND_TO_EVEN: -inf
  __CPROVER_rounding_mode = ROUND_TO_EVEN;
  float rn0 = c / b;
  assert(isinf(rn0) && rn0 < 0);

  // ROUND_TO_MINUS_INF: directed toward -inf -> -inf
  __CPROVER_rounding_mode = ROUND_TO_MINUS_INF;
  float rn1 = c / b;
  assert(isinf(rn1) && rn1 < 0);

  // ROUND_TO_PLUS_INF: directed toward +inf -> -FLT_MAX
  __CPROVER_rounding_mode = ROUND_TO_PLUS_INF;
  float rn2 = c / b;
  assert(rn2 == -FLT_MAX);

  // ROUND_TO_AWAY: round-to-nearest -> -inf (negative overflow).
  __CPROVER_rounding_mode = ROUND_TO_AWAY;
  float rn4 = c / b;
  assert(isinf(rn4) && rn4 < 0);

  // ---- bug 1 coverage (exponent wraparound on large quotient) ----

  // FLT_MAX / FLT_MIN: unbiased exponent of the quotient is
  // 127 - (-126) + 23 = 276, which would overflow the signed 9-bit
  // (spec.e + 1) intermediate in the buggy float_bvt::div; after the fix
  // it is 10-bit signed.
  //
  // These cases exercise the widened-exponent path but cannot *pin* bug 1:
  // the result is identical on the pre-fix and post-fix encoders, so they
  // pass on develop too. The reason is structural, not luck. The largest
  // intermediate that float_bvt::div can produce is FLT_MAX / FLT_TRUE_MIN,
  // i.e. 127 - (-149) + 23 = 299; wrapping that in the buggy 9-bit signed
  // type always lands deeply negative (<= -213), i.e. in the underflow
  // range, never on a spurious in-range finite exponent (which would need a
  // value in [386, 639]). The downstream normalization/denormalization path
  // then recovers the correct saturation, so no C-level input can
  // distinguish the two encoders. The real safeguard for fix 1 is therefore
  // parity with float_utilst::div (which has used spec.e + 2 since 2017) and
  // with float_bvt::mul, not this test.
  __CPROVER_rounding_mode = ROUND_TO_ZERO;
  float fmm_max = FLT_MAX / FLT_MIN;
  assert(fmm_max == FLT_MAX);

  __CPROVER_rounding_mode = ROUND_TO_EVEN;
  float fmm_inf = FLT_MAX / FLT_MIN;
  assert(isinf(fmm_inf) && fmm_inf > 0);

  // DBL_MAX / DBL_MIN: unbiased exponent of the quotient is
  // 1023 - (-1022) + 52 = 2097, which would overflow signed 12-bit
  // (spec.e + 1 = 12 for double). Same caveat as the float case: the
  // largest intermediate (DBL_MAX / DBL_TRUE_MIN = 1023 - (-1074) + 52 =
  // 2149) wraps to <= -1947 in the buggy 12-bit type -- deep underflow, not
  // a spurious in-range finite (which would need [3074, 5119]) -- so the
  // result is again indistinguishable from the fixed encoder.
  __CPROVER_rounding_mode = ROUND_TO_ZERO;
  double dmm_max = DBL_MAX / DBL_MIN;
  assert(dmm_max == DBL_MAX);

  __CPROVER_rounding_mode = ROUND_TO_EVEN;
  double dmm_inf = DBL_MAX / DBL_MIN;
  assert(isinf(dmm_inf) && dmm_inf > 0);

  return 0;
}
