// Non-deterministic x86 80-bit extended `long double` values include
// unnormals (integer bit 0 with a non-zero exponent), which are NaN.  They
// must not satisfy range constraints and then yield values outside that
// range in arithmetic or conversions.
//
// The test is hermetic (no system headers) and provided as `nondet.i` so
// CBMC parses it without invoking the host's preprocessor.

int main(void)
{
  long double x, y;
  __CPROVER_assume(x > 1.0L && x < 2.0L && y > 1.0L && y < 2.0L);

  long double z = x * y;
  __CPROVER_assert(z > 1.0L && z < 4.0L, "product range");
  __CPROVER_assert(x * 1.0L > 1.0L, "multiplication by one");

  double d = (double)x;
  __CPROVER_assert(d >= 1.0 && d <= 2.0, "conversion to double");

  return 0;
}
