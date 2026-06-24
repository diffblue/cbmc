// Converting an integer to x86 80-bit extended `long double` is a
// floatbv_typecast whose SMT2 bit-vector lowering calls a
// `float_bv.floatbv_typecast_*` helper; that helper has to be registered
// by `smt2_convt::find_symbols` even though the *operand* is an integer
// (not a bit-vector-encoded float).  This is exactly the gap the
// "register float_bv typecast helper for bit-vector-encoded results"
// change closes.
//
// The test pins `--arch x86_64` (via test.desc) so the x86 80-bit
// extended layout is selected on every target.  It deliberately calls no
// library function, so CBMC never has to preprocess the library for the
// x86_64 target -- the test is fully host-independent (it does not need
// an x86_64-capable system preprocessor) and is provided pre-processed as
// `main.i`.  Every int32 value is exactly representable in x86 80-bit
// extended, so the conversions below are exact.

int main(void)
{
  int i;
  long double x = (long double)i;

  if(i > 0)
    __CPROVER_assert(x > 0.0l, "positive int -> positive long double");
  if(i == 0)
    __CPROVER_assert(x == 0.0l, "zero int -> zero long double");
  if(i < 0)
    __CPROVER_assert(x < 0.0l, "negative int -> negative long double");

  long double c = (long double)42;
  __CPROVER_assert(c == 42.0l, "42 -> 42.0L");

  return 0;
}
