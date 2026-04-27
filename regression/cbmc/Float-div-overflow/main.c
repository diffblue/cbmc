// Test that division overflow is handled correctly under directed rounding.
//
// Bug: float_bvt extended the exponent by only 1 bit instead of 2 in the
// division, causing exponent wraparound for large quotients.
//
// FLT_MAX / 0.5f overflows.  Under directed rounding modes that point
// away from infinity, the result should be FLT_MAX (not inf).

#include <assert.h>
#include <float.h>
#include <math.h>

extern int __CPROVER_rounding_mode;

int main()
{
  float a, b;
  __CPROVER_assume(a == FLT_MAX);
  __CPROVER_assume(b == 0.5f);

  // ROUND_TO_EVEN: overflow -> +inf
  __CPROVER_rounding_mode = 0;
  float r0 = a / b;
  assert(isinf(r0) && r0 > 0);

  // ROUND_TO_ZERO: overflow, directed toward zero -> FLT_MAX
  __CPROVER_rounding_mode = 3;
  float r3 = a / b;
  assert(r3 == FLT_MAX);

  // ROUND_TO_PLUS_INF: positive overflow, directed toward +inf -> +inf
  __CPROVER_rounding_mode = 2;
  float r2 = a / b;
  assert(isinf(r2) && r2 > 0);

  // ROUND_TO_MINUS_INF: positive overflow, directed toward -inf -> FLT_MAX
  __CPROVER_rounding_mode = 1;
  float r1 = a / b;
  assert(r1 == FLT_MAX);

  // Negative overflow: -FLT_MAX / 0.5f
  float c;
  __CPROVER_assume(c == -FLT_MAX);

  // ROUND_TO_EVEN: -inf
  __CPROVER_rounding_mode = 0;
  float rn0 = c / b;
  assert(isinf(rn0) && rn0 < 0);

  // ROUND_TO_MINUS_INF: negative overflow toward -inf -> -inf
  __CPROVER_rounding_mode = 1;
  float rn1 = c / b;
  assert(isinf(rn1) && rn1 < 0);

  // ROUND_TO_PLUS_INF: negative overflow toward +inf -> -FLT_MAX
  __CPROVER_rounding_mode = 2;
  float rn2 = c / b;
  assert(rn2 == -FLT_MAX);

  return 0;
}
