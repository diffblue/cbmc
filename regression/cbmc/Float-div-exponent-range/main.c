// Test division where subtracting the exponents leaves the range of the
// operands' exponent type.

#include <assert.h>
#include <float.h>

int main()
{
  // 2^127 / 2^-126 = 2^253 overflows to infinity.
  float a, b;
  __CPROVER_assume(a == 0x1p127f);
  __CPROVER_assume(b == 0x1p-126f);
  float r = a / b;
  assert(r == __builtin_inff());

  // 2^-126 / 2^127 = 2^-253 underflows to zero.
  float c, d;
  __CPROVER_assume(c == 0x1p-126f);
  __CPROVER_assume(d == 0x1p127f);
  float r2 = c / d;
  assert(r2 == 0.0f);

  // FLT_MAX / 2^-149 overflows to infinity.
  float e, f;
  __CPROVER_assume(e == FLT_MAX);
  __CPROVER_assume(f == 0x1p-149f);
  float r3 = e / f;
  assert(r3 == __builtin_inff());

  // A format with a narrow exponent (4 bits, bias 7) and 23 fraction bits,
  // where adding spec.f to the exponent difference exceeds even the range
  // of spec.e + 2 bits.
  typedef __CPROVER_floatbv[28][23] narrow_exponent_floatt;
  narrow_exponent_floatt g, h;
  __CPROVER_assume(g == (narrow_exponent_floatt)1.0f);
  __CPROVER_assume(h == (narrow_exponent_floatt)3.0f);
  narrow_exponent_floatt r4 = g / h;
  assert(r4 == (narrow_exponent_floatt)(1.0f / 3.0f));

  // 2^7 / 2^-6 = 2^13 overflows to infinity in this format.
  narrow_exponent_floatt i, j;
  __CPROVER_assume(i == (narrow_exponent_floatt)0x1p7f);
  __CPROVER_assume(j == (narrow_exponent_floatt)0x1p-6f);
  narrow_exponent_floatt r5 = i / j;
  assert(r5 == (narrow_exponent_floatt)__builtin_inff());

  return 0;
}
