// Division overflow under all rounding modes, in both encoders (float_utilst
// for the SAT back end, float_bvt for the SMT back end, see test_smt.desc).
//
// round_exponent did not include ROUND_TO_AWAY in overflow_to_inf. As
// ROUND_TO_AWAY is a round-to-nearest mode, overflow must produce +-inf. The
// ROUND_TO_AWAY cases below pin that fix. The operands are not constant, so
// that the division is not constant-folded.

#include <assert.h>
#include <float.h>
#include <math.h>

// Rounding-mode encoding mirrors src/util/ieee_float.h. Values 0-3 match
// the x86 rounding-control field; 4 (ties-away) is CBMC-specific.
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

  // ROUND_TO_ZERO: directed toward zero -> -FLT_MAX
  __CPROVER_rounding_mode = ROUND_TO_ZERO;
  float rn3 = c / b;
  assert(rn3 == -FLT_MAX);

  // ROUND_TO_AWAY: round-to-nearest -> -inf (negative overflow).
  __CPROVER_rounding_mode = ROUND_TO_AWAY;
  float rn4 = c / b;
  assert(isinf(rn4) && rn4 < 0);

  return 0;
}
