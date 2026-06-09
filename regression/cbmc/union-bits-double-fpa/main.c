#include <stdint.h>

// Inverse of regression/cbmc/union-double-bits-fpa: write the IEEE-754
// bit pattern of a double into a union and then read the double field.
// Under `--cprover-smt2` this forces the SMT2 back-end to emit the
// single-operand bit-pattern overload of `to_fp` for the FP read of
// the union:
//
//   ((_ to_fp 11 53) <bv64>)
//
// CPROVER's smt2 parser previously rejected this overload with
// "unexpected token in an expression"; the parser now recognises it
// and routes it through a bit-level reinterpret typecast.  Without
// `--no-simplify` the constant union read would be folded away
// before reaching the back-end, so the parser entry is actually
// exercised.
//
// `double` is IEEE binary64 on every supported target, so no
// architecture pinning is needed.

int main(void)
{
  union
  {
    double d;
    uint64_t bits;
  } u;

  u.bits = 0x3FF0000000000000ULL;
  __CPROVER_assert(u.d == 1.0, "bit pattern 0x3FF0... reinterprets as 1.0");

  u.bits = 0xC000000000000000ULL;
  __CPROVER_assert(u.d == -2.0, "bit pattern 0xC000... reinterprets as -2.0");

  u.bits = 0x0000000000000000ULL;
  __CPROVER_assert(u.d == 0.0, "all-zero bits reinterpret as +0.0");

  return 0;
}
