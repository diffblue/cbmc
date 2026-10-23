// Regression test for the float_bvt fmod/remainder large-quotient bug.
//
// The previous float_bvt::rem/mod computed fmod as x - trunc(x/y)*y, with
// the quotient truncated to a fixed (type-width) integer.  When floor(x/y)
// exceeds that width it wraps around, giving a wrong result.  Run via the
// bit-vector SMT encoding (cbmc --z3) this used to FAIL; with the
// integer-significand fmod it is correct.  The default boolbv path
// (float_utilst) was always correct and is exercised here too.
//
// The float_bvt encoding is generic over the float width, so triggering the
// bug only needs floor(x/y) to exceed the type-width truncation: 2^33 for
// float (just past 32 bits) and 2^16 for _Float16 (just past 16 bits).  All
// operands are exact multiples, so every result is 0.
//
// Two deliberate choices keep the bit-vector SMT (cbmc --z3) formula
// tractable:
//   * the float quotient is the smallest that still overflows the 32-bit
//     truncation (2^33) -- the formula grows with the exponent difference,
//     so larger quotients such as 2^50 time the solver out; and
//   * float remainderf is not checked here.  Its round-to-nearest
//     tie-breaking roughly doubles the formula and is intractable for z3
//     even at 2^33.  Its large-quotient behaviour is covered symbolically
//     on the boolbv path by bench.c, and the remainder fix on the
//     (type-generic) float_bvt path is exercised here via _Float16.

float __CPROVER_fmodf(float, float);

int main()
{
  float x = 0x1p23f, y = 0x1p-10f; // x / y = 2^33
  __CPROVER_assert(__CPROVER_fmodf(x, y) == 0.0f, "fmodf large quotient");

#if defined(__GNUC__) && __GNUC__ >= 13
  _Float16 __CPROVER_fmodf16(_Float16, _Float16);
  _Float16 __CPROVER_remainderf16(_Float16, _Float16);
  _Float16 a = (_Float16)2048.0, b = (_Float16)0.03125; // a / b = 2^16
  __CPROVER_assert(
    __CPROVER_fmodf16(a, b) == (_Float16)0.0, "fmodf16 large quotient");
  __CPROVER_assert(
    __CPROVER_remainderf16(a, b) == (_Float16)0.0,
    "remainderf16 large quotient");
#endif
}
