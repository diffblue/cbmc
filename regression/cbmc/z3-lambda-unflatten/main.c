// Pins the SMT2 we emit under --z3 when set_to() defines a symbol whose
// body would otherwise be a `(define-fun ... (lambda ...))`.
//
// Z3 rejects `(get-value ...)` on symbols whose `define-fun` body
// contains a lambda, so smt2_convt::set_to switches to
// `(declare-fun X () T) (assert (= X body))` whenever
// use_lambda_for_array is set (currently only Z3).  This test
// exercises the path -- the variable-length unsigned-char array
// `src` ends up encoded with an `array_comprehension` that produces a
// lambda body, and the new gate keeps the assignment to the
// memcpy-source symbol parseable by Z3's get-value while still
// emitting the lambda in an `assert (= ...)`.
//
// A future change that re-enables `use_as_const = true` for Z3 (i.e.
// once Z3Prover/z3#9550 is fixed and we bump the minimum Z3 version)
// must also update or remove this regex; the test exists precisely to
// flag such a silent regression.

#include <stdint.h>
#include <string.h>

int main()
{
  unsigned char size;
  __CPROVER_assume(size > 1);
  __CPROVER_assume(size < 5);
  __CPROVER_assume(size % 4 == 0);
  unsigned char src[size];
  src[0] = 0x2a;
  src[1] = 0x2a;
  src[2] = 0x2a;
  src[3] = 0x2a;
  int32_t dest;
  memcpy(&dest, src, size);
  __CPROVER_assert(dest == 0x2a2a2a2a, "memcpy round-trip");
  return 0;
}
