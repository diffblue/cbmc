// Test division with a subnormal dividend.
//
// Bug: float_utilst and float_bvt divided the unpacked fractions directly.
// A subnormal dividend has leading zeros in its fraction, so the quotient
// had too few significant bits whenever the result was normal (or a
// subnormal with more significant bits than the dividend), which led to
// wrong rounding or plain truncation.

#include <assert.h>
#include <float.h>

int main()
{
  // Smallest positive subnormal divided by three times the smallest
  // subnormal: mathematically 1/3, whose IEEE-754 round-to-nearest-even
  // value is 0x1.555556p-2.  The buggy build returned 0x1.555554p-2
  // (1 ULP low) because the sticky bit was lost.
  float a, b;
  __CPROVER_assume(a == 0x1p-149f);
  __CPROVER_assume(b == 0x3p-149f);
  float r = a / b;
  assert(r == 0x1.555556p-2f);

  // A second subnormal/subnormal case, 7/4 = 1.75 exactly.
  float c, d;
  __CPROVER_assume(c == 0x7p-149f);
  __CPROVER_assume(d == 0x4p-149f);
  float r2 = c / d;
  assert(r2 == 0x1.cp+0f);

  // Exact subnormal/normal sanity check: FLT_MIN is the smallest positive
  // normal float; FLT_MIN * 0.5f is subnormal, and dividing it by 2 stays
  // exactly representable.
  float e, f;
  __CPROVER_assume(e == FLT_MIN * 0.5f);
  __CPROVER_assume(f == 2.0f);
  float r3 = e / f;
  assert(r3 == FLT_MIN * 0.25f);

  // Subnormal divided by a normal that is smaller than one: the result is
  // normal and needs rounding.  The buggy build returned 0x1.4p-24 because
  // the quotient retained only two significant bits.
  float g, h;
  __CPROVER_assume(g == 0x1p-149f);
  __CPROVER_assume(h == 0x1.8p-126f);
  float r4 = g / h;
  assert(r4 == 0x1.555556p-24f);

  // A format with a narrow exponent (4 bits, bias 7) and 23 fraction bits:
  // the smallest subnormal (2^-29) has 23 leading zeros in its fraction, and
  // normalizing it yields an unbiased exponent of -29, which does not fit
  // into the 4-bit exponent.
  typedef __CPROVER_floatbv[28][23] narrow_exponent_floatt;
  narrow_exponent_floatt i, j;
  __CPROVER_assume(i == (narrow_exponent_floatt)0x1p-29f);
  __CPROVER_assume(j == (narrow_exponent_floatt)0x1p-6f);
  narrow_exponent_floatt r5 = i / j;
  assert(r5 == (narrow_exponent_floatt)0x1p-23f);

  return 0;
}
