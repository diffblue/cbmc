#include <stdint.h>

// Exercises smt2_convt::flatten2bv on an FPA-encoded `double`: reading the
// bytes of a double through a union forces the SMT2 back-end to turn the
// floating-point value into its IEEE-754 interchange bit pattern.  The
// SMT-LIB FloatingPoint theory has no operator for that bit pattern
// (fp.to_ubv / fp.to_sbv are value conversions, not a bit-pattern
// reinterpret), so before this was supported the cprover-smt2 / FPA path
// hit an invariant here.  `--no-simplify` keeps the constant from being
// folded away before it reaches the back-end, so the flattening code is
// actually exercised.
//
// The check is meaningful primarily under the cprover-smt2 profile (FPA
// theory); under the SAT back-end the value is bit-vector-encoded anyway,
// in which case the assertions simply hold.

int main(void)
{
  union
  {
    double d;
    uint64_t bits;
  } u;

  u.d = 1.0;
  __CPROVER_assert(u.bits == 0x3FF0000000000000ull, "IEEE-754 bits of 1.0");

  u.d = -2.0;
  __CPROVER_assert(u.bits == 0xC000000000000000ull, "IEEE-754 bits of -2.0");

  u.d = 0.0;
  __CPROVER_assert(u.bits == 0x0000000000000000ull, "IEEE-754 bits of 0.0");

  return 0;
}
