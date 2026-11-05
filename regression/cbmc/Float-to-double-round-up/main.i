// Converting a value just below 2 from a format with a wider significand
// to double rounds up to 2.0, which carries into the exponent.

int main(void)
{
  long double y;
  __CPROVER_assume(y > 1.0L && y < 2.0L);
  double e = (double)y;
  __CPROVER_assert(e >= 1.0 && e <= 2.0, "conversion stays in range");
  return 0;
}
