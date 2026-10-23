// Pure long-double FP arithmetic.  No byte-level access to the
// underlying storage, so no bv<->FP boundary; this exercises the FP
// semantics on long double across all four CBMC back-ends.
//
// On x86_64 with x86 80-bit extended `long double`, the arithmetic
// semantics match IEEE binary79 for valid encodings (and our SAT
// backend encodes the layout precisely), so the assertions below hold
// under SAT, --z3, --cprover-smt2 and --incremental-smt2-solver.
//
// This complements the byte-layout tests, which exercise the FP<->bv
// boundary and are restricted to back-ends that fully support it.
//
// The test is hermetic (no system headers) and provided as `main.i`
// so CBMC parses it without invoking the host's preprocessor.  It can
// therefore run on any host -- including FreeBSD/OpenBSD CI runners
// that don't ship with gcc and arm64 Linux runners that don't have
// x86_64 cross-compilation tooling -- as long as the test.desc fixes
// `--arch x86_64 --os linux` so CBMC models x86 80-bit extended
// regardless of the host's native long-double layout.

int main(void)
{
  // 1. Exact addition / multiplication / division on representable
  //    values.
  long double a = 1.0L;
  long double b = 2.0L;
  long double c = a + b;
  __CPROVER_assert(c == 3.0L, "1.0L + 2.0L == 3.0L");

  long double d = c * 2.0L;
  __CPROVER_assert(d == 6.0L, "3.0L * 2.0L == 6.0L");

  long double e = d / 3.0L;
  __CPROVER_assert(e == 2.0L, "6.0L / 3.0L == 2.0L");

  // 2. Sign preservation under negation.
  long double f = 3.5L;
  __CPROVER_assert(-f < 0.0L, "negation gives < 0");
  __CPROVER_assert(f > 0.0L, "positive is > 0");
  __CPROVER_assert(-(-f) == f, "double negation");

  // 3. Long double has 64 bits of significand precision (well above
  //    the 53 bits of binary64), so 1.0L + 2^-60 must not equal
  //    1.0L.  This would round to 1.0 if the model were treating long
  //    double as `double`.
  long double tiny = 1.0L;
  for(int i = 0; i < 60; ++i)
    tiny /= 2.0L;
  long double almost_one = 1.0L + tiny;
  __CPROVER_assert(almost_one != 1.0L, "long double has > 60 bits precision");

  // 4. Reciprocal of a wide-range value: 1/x for very large x is
  //    positive and finite.  At 2^-100 the result is comfortably
  //    *normal* in extended precision (whose subnormal threshold is
  //    around 2^-16382), so this exercises the wide exponent range
  //    rather than subnormal handling.  TODO: add a separate test
  //    for genuine subnormal arithmetic once the pack/unpack of
  //    canonical x86 denormals is exercised end-to-end.
  long double large = 1.0L;
  for(int i = 0; i < 100; ++i)
    large *= 2.0L;
  long double recip = 1.0L / large;
  __CPROVER_assert(recip > 0.0L, "1/2^100 > 0");
  __CPROVER_assert(recip < 1.0L, "1/2^100 < 1");

  return 0;
}
