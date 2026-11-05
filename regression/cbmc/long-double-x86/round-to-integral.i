// Rounding x86 80-bit extended `long double` values to integers.  The
// integer bit is explicit, so rounding up past a power of two must set it
// for the new exponent.
//
// The test is hermetic (no system headers) and provided as
// `round-to-integral.i` so CBMC parses it without invoking the host's
// preprocessor.

int main(void)
{
  long double a, b, c, d, e, f;
  __CPROVER_assume(a == -2.5L);
  __CPROVER_assume(b == -2.3L);
  __CPROVER_assume(c == 2.7L);
  __CPROVER_assume(d == -0.5L);
  __CPROVER_assume(e == 1.75L);
  __CPROVER_assume(f == 0x1.fffffffffffffffep62L); // 2^63 - 1/2

  // Rounding modes: 0 to nearest (ties to even), 1 downward, 2 upward,
  // 3 towards zero, 4 to nearest (ties away from zero).
  __CPROVER_assert(__CPROVER_round_to_integralld(a, 0) == -2.0L, "rint -2.5");
  __CPROVER_assert(__CPROVER_round_to_integralld(b, 1) == -3.0L, "floor -2.3");
  __CPROVER_assert(__CPROVER_round_to_integralld(b, 2) == -2.0L, "ceil -2.3");
  __CPROVER_assert(__CPROVER_round_to_integralld(c, 3) == 2.0L, "trunc 2.7");
  __CPROVER_assert(__CPROVER_round_to_integralld(d, 4) == -1.0L, "round -0.5");
  __CPROVER_assert(__CPROVER_round_to_integralld(e, 0) == 2.0L, "rint 1.75");
  __CPROVER_assert(
    __CPROVER_isnormalld(__CPROVER_round_to_integralld(e, 2)), "ceil 1.75");
  __CPROVER_assert(
    __CPROVER_round_to_integralld(f, 4) == 0x1p63L, "round 2^63 - 1/2");

  return 0;
}
