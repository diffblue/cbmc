// Round-to-integral (rintf, rint) under all rounding modes, for special
// values, denormals, ties, already-integral values, and formats with a narrow
// exponent. Each input and each rounding mode is nondeterministic, pinned to
// a value by an assumption, so that the simplifier does not fold the
// operation and the back-end's encoding is exercised.
//
// Previously, `cbmc --smt2 --z3` (the non-FPA SMT path, exercised by
// test_smt.desc) hit an UNEXPECTEDCASE invariant in
// smt2_conv.cpp::convert_floatbv_round_to_integral, and the flattening back
// end returned infinity for the narrow-exponent format, as its 2^f magic
// number was not representable.

#include <assert.h>
#include <float.h>
#include <math.h>

extern int __CPROVER_rounding_mode;

static int mode(int m)
{
  int r;
  __CPROVER_assume(r == m);
  return r;
}

static float nd_float(float v)
{
  float r;
  __CPROVER_assume(r == v);
  return r;
}

static double nd_double(double v)
{
  double r;
  __CPROVER_assume(r == v);
  return r;
}

int main()
{
  // Rounding-mode encoding (matches ieee_floatt::rounding_modet):
  //   0 = ROUND_TO_EVEN
  //   1 = ROUND_TO_MINUS_INF
  //   2 = ROUND_TO_PLUS_INF
  //   3 = ROUND_TO_ZERO
  //   4 = ROUND_TO_AWAY

  // ROUND_TO_EVEN: ties round to even.
  __CPROVER_rounding_mode = mode(0);
  float a = nd_float(2.5f);
  float r1 = rintf(a);
  assert(r1 == 2.0f);

  __CPROVER_rounding_mode = mode(0);
  float b = nd_float(3.5f);
  float r2 = rintf(b);
  assert(r2 == 4.0f);

  // Negative ties under ROUND_TO_EVEN.
  __CPROVER_rounding_mode = mode(0);
  float bn1 = nd_float(-2.5f);
  float rn1 = rintf(bn1);
  assert(rn1 == -2.0f);

  __CPROVER_rounding_mode = mode(0);
  float bn2 = nd_float(-3.5f);
  float rn2 = rintf(bn2);
  assert(rn2 == -4.0f);

  // ROUND_TO_PLUS_INF (ceil).
  __CPROVER_rounding_mode = mode(2);
  float c = nd_float(2.3f);
  float r3 = rintf(c);
  assert(r3 == 3.0f);

  // ROUND_TO_MINUS_INF (floor).
  __CPROVER_rounding_mode = mode(1);
  float d = nd_float(2.7f);
  float r4 = rintf(d);
  assert(r4 == 2.0f);

  // ROUND_TO_ZERO (truncate).
  __CPROVER_rounding_mode = mode(3);
  float e = nd_float(-2.7f);
  float r5 = rintf(e);
  assert(r5 == -2.0f);

  // ROUND_TO_AWAY: 0.5 rounds away from zero.
  __CPROVER_rounding_mode = mode(4);
  float aw1 = nd_float(0.5f);
  float r_aw1 = rintf(aw1);
  assert(r_aw1 == 1.0f);

  __CPROVER_rounding_mode = mode(4);
  float aw2 = nd_float(-0.5f);
  float r_aw2 = rintf(aw2);
  assert(r_aw2 == -1.0f);

  __CPROVER_rounding_mode = mode(4);
  float aw3 = nd_float(2.5f);
  float r_aw3 = rintf(aw3);
  assert(r_aw3 == 3.0f);

  // Already-integral input (small).
  __CPROVER_rounding_mode = mode(0);
  float f = nd_float(42.0f);
  float r6 = rintf(f);
  assert(r6 == 42.0f);

  // Values of at least 2^23 are integral.
  __CPROVER_rounding_mode = mode(0);
  float big_int = nd_float(16777216.0f);
  float r_big = rintf(big_int);
  assert(r_big == 16777216.0f);

  // Special values: should pass through unchanged via is_special.
  // NaN.
  __CPROVER_rounding_mode = mode(0);
  float nan_in;
  __CPROVER_assume(isnan(nan_in));
  float r_nan = rintf(nan_in);
  assert(isnan(r_nan));

  // +Infinity.
  __CPROVER_rounding_mode = mode(0);
  float inf_pos;
  __CPROVER_assume(inf_pos == INFINITY);
  float r_ip = rintf(inf_pos);
  assert(isinf(r_ip) && r_ip > 0);

  // -Infinity.
  __CPROVER_rounding_mode = mode(0);
  float inf_neg;
  __CPROVER_assume(inf_neg == -INFINITY);
  float r_in = rintf(inf_neg);
  assert(isinf(r_in) && r_in < 0);

  // +0.0.
  __CPROVER_rounding_mode = mode(0);
  float pz = nd_float(0.0f);
  float r_pz = rintf(pz);
  assert(r_pz == 0.0f);

  // -0.0 should preserve sign under any mode.
  __CPROVER_rounding_mode = mode(0);
  float nz;
  __CPROVER_assume(nz == 0.0f && signbit(nz));
  float r_nz = rintf(nz);
  assert(r_nz == 0.0f); // both ±0 compare equal to 0
  assert(signbit(r_nz));

  // Subnormals: rintf of a positive denormal under ROUND_TO_EVEN -> +0.
  __CPROVER_rounding_mode = mode(0);
  float den = nd_float(FLT_MIN / 2.0f);
  float r_den = rintf(den);
  assert(r_den == 0.0f);

  // Subnormal under ROUND_TO_PLUS_INF (ceil) -> +1.
  __CPROVER_rounding_mode = mode(2);
  float den2 = nd_float(FLT_MIN / 2.0f);
  float r_den2 = rintf(den2);
  assert(r_den2 == 1.0f);

  // double / rint, which have a 53-bit significand.
  __CPROVER_rounding_mode = mode(0);
  double da = nd_double(2.5);
  double dr1 = rint(da);
  assert(dr1 == 2.0);

  __CPROVER_rounding_mode = mode(0);
  double db = nd_double(3.5);
  double dr2 = rint(db);
  assert(dr2 == 4.0);

  __CPROVER_rounding_mode = mode(1);
  double dc = nd_double(-2.7);
  double dr3 = rint(dc);
  assert(dr3 == -3.0);

  // Values of at least 2^52 are integral.
  __CPROVER_rounding_mode = mode(0);
  double dbig = nd_double(9007199254740992.0);
  double dr_big = rint(dbig);
  assert(dr_big == 9007199254740992.0);

  // A format with a narrow exponent (4 bits, bias 7) and 23 fraction bits:
  // f = 23 is not representable as an unbiased exponent, and 2^23 is not a
  // finite value of this format.
  typedef __CPROVER_floatbv[28][23] narrow_exponent_floatt;
  __CPROVER_rounding_mode = mode(0);
  narrow_exponent_floatt na;
  __CPROVER_assume(na == (narrow_exponent_floatt)2.5f);
  narrow_exponent_floatt nr1 = __CPROVER_round_to_integralf(na, mode(0));
  assert(nr1 == (narrow_exponent_floatt)2.0f);

  narrow_exponent_floatt nb;
  __CPROVER_assume(nb == (narrow_exponent_floatt)-0x1.fffffep7f);
  narrow_exponent_floatt nr2 = __CPROVER_round_to_integralf(nb, mode(3));
  assert(nr2 == (narrow_exponent_floatt)-255.0f);

  // Rounding up the largest finite value overflows to infinity, as 256 is
  // not a finite value of this format.
  narrow_exponent_floatt nc;
  __CPROVER_assume(nc == (narrow_exponent_floatt)0x1.fffffep7f);
  narrow_exponent_floatt nr3 = __CPROVER_round_to_integralf(nc, mode(0));
  assert(nr3 == (narrow_exponent_floatt)INFINITY);

  // A 2-bit exponent (bias 1), in which 0.5 and 0.25 are subnormal.
  typedef __CPROVER_floatbv[5][2] e2_floatt;
  e2_floatt ta, tb;
  __CPROVER_assume(ta == (e2_floatt)0.5f);
  __CPROVER_assume(tb == (e2_floatt)0.25f);
  assert(__CPROVER_round_to_integralf(ta, mode(0)) == 0);
  assert(__CPROVER_round_to_integralf(ta, mode(4)) == 1);
  assert(__CPROVER_round_to_integralf(tb, mode(0)) == 0);
  assert(__CPROVER_round_to_integralf(tb, mode(4)) == 0);
  assert(__CPROVER_round_to_integralf(tb, mode(2)) == 1);

  // A 1-bit exponent (bias 0), in which there are no normal numbers.
  typedef __CPROVER_floatbv[4][2] e1_floatt;
  e1_floatt tc, td;
  __CPROVER_assume(tc == (e1_floatt)1.0f);
  __CPROVER_assume(td == (e1_floatt)0.5f);
  assert(__CPROVER_round_to_integralf(tc, mode(0)) == tc);
  assert(__CPROVER_round_to_integralf(td, mode(4)) == (e1_floatt)1.0f);

  // Rounding-mode arguments of different integer types.
  float x1 = nd_float(2.5f), x2 = nd_float(2.5f);
  signed char m = (signed char)mode(4);
  assert(__CPROVER_round_to_integralf(x1, mode(0)) == 2.0f);
  assert(__CPROVER_round_to_integralf(x2, m) == 3.0f);

  return 0;
}
