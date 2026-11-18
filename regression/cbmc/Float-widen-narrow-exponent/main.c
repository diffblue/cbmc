// Widening a floating-point value normalises its significand. For target
// formats whose fraction is wide relative to the exponent, e.g., an 8-bit
// fraction (9 bits with the hidden bit) and a 3-bit exponent, the shifter
// needs more stages than the exponent of the source has bits.
typedef __CPROVER_floatbv[4][1] narrow_t; // e = 2, f = 1, bias 1
typedef __CPROVER_floatbv[12][8] wide8_t; // e = 3, f = 8
typedef __CPROVER_floatbv[13][9] wide9_t; // e = 3, f = 9

int main()
{
  narrow_t subnormal, one, one_and_half, max, negative;
  __CPROVER_assume(subnormal == (narrow_t)0.5f);
  __CPROVER_assume(one == (narrow_t)1.0f);
  __CPROVER_assume(one_and_half == (narrow_t)1.5f);
  __CPROVER_assume(max == (narrow_t)3.0f);
  __CPROVER_assume(negative == (narrow_t)-0.5f);

  wide8_t a = subnormal, b = one, c = one_and_half, d = max, e = negative;
  __CPROVER_assert(a == (wide8_t)0.5f, "subnormal to [12][8]");
  __CPROVER_assert(b == (wide8_t)1.0f, "1 to [12][8]");
  __CPROVER_assert(c == (wide8_t)1.5f, "1.5 to [12][8]");
  __CPROVER_assert(d == (wide8_t)3.0f, "3 to [12][8]");
  __CPROVER_assert(e == (wide8_t)-0.5f, "-subnormal to [12][8]");

  wide9_t f = subnormal, g = max;
  __CPROVER_assert(f == (wide9_t)0.5f, "subnormal to [13][9]");
  __CPROVER_assert(g == (wide9_t)3.0f, "3 to [13][9]");
  return 0;
}
