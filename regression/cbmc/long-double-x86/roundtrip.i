// Round-trip casts between `double` and x86 80-bit extended `long
// double`.  The 80-bit format has a strictly wider value range and more
// mantissa bits than `double`, so any finite double-precision value
// promoted to long double must round-trip exactly back to its original
// double bit pattern.
//
// The test is hermetic (no system headers) and provided as `main.i` so
// CBMC parses it without invoking the host's preprocessor.  The
// test.desc fixes `--arch x86_64 --os linux` so CBMC models x86 80-bit
// extended regardless of the host's native long-double layout.

typedef unsigned long long u64;

int main(void)
{
  // 1. A handful of finite double constants round-trip exactly through
  //    `long double`.  We compare the bit patterns directly via union
  //    aliasing.
  union double_bits
  {
    double d;
    u64 i;
  };

  double samples[] = {
    0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 1024.0, 1.0 / 3.0};
  const int n = sizeof(samples) / sizeof(samples[0]);

  for(int i = 0; i < n; ++i)
  {
    long double promoted = (long double)samples[i];
    double demoted = (double)promoted;
    union double_bits before;
    union double_bits after;
    before.d = samples[i];
    after.d = demoted;
    __CPROVER_assert(before.i == after.i, "double -> long double -> double");
  }

  // 2. A nondet finite double round-trips bit-for-bit (excluding NaN
  //    and +/-infinity, which require comparison via bit patterns
  //    rather than ==).
  double d;
  __CPROVER_assume(d == d);                            // not NaN
  __CPROVER_assume(d != 1.0 / 0.0 && d != -1.0 / 0.0); // not infinity

  long double promoted = (long double)d;
  double demoted = (double)promoted;
  __CPROVER_assert(d == demoted, "symbolic double round-trips");

  // 3. Sign is preserved through a double -> long double promotion.
  if(d < 0.0)
    __CPROVER_assert(promoted < 0.0L, "sign preserved (negative)");
  if(d > 0.0)
    __CPROVER_assert(promoted > 0.0L, "sign preserved (positive)");

  return 0;
}
