#include <stdint.h>

// Regression test for float-to-integer conversion in the SMT2 back-end
// (float_bvt::to_integer in src/solvers/floatbv/float_bv.cpp).
//
// The correct algorithm pads the unpacked fraction (spec.f+1 bits) with
// low-order zeros to dest_width, then right-shifts so the hidden bit lands at
// bit position `exponent` in the result.  The old SMT2 code skipped the
// padding step, which broke for exponent > spec.f (i.e. |f| >= 2^53 for
// double): the hidden bit was already at the top of the unpadded
// spec.f+1-bit fraction and needed to move UP, but a right shift can only
// move bits down.
//
// Bit-level walkthrough using a tiny spec.f=3 (4-bit fraction) and
// dest_width=8, for the value 16.0 = 1.000 * 2^4 (exponent=4 > spec.f=3,
// the same boundary as 2^53 for double):
//
//   The goal: right-shift the fraction so the hidden bit lands at bit
//   position `exponent` (=4) in the result, giving it the value 2^4=16.
//   distance = (current position of hidden bit) - (target position)
//            = (shift_width - 1) - exponent
//
//   WITHOUT the fix (shift the 4-bit fraction directly, shift_width=4):
//     fraction (4 bits):  1000   hidden bit at position 3
//     distance = (4-1) - 4 = -1  (hidden bit is already BELOW its target)
//     -1 as unsigned = a huge shift amount
//     1000 >> huge    = 0000      hidden bit shifted off the bottom
//     result: 0                   <-- WRONG, spurious VERIFICATION FAILED
//
//   WITH the fix (pad to dest_width=8 first, shift_width=8):
//     1000 -> 1000 0000           hidden bit now at position 7
//     distance = (8-1) - 4 = 3   (hidden bit is above its target, shift down)
//     1000 0000 >> 3 = 0001 0000 = 16  <-- CORRECT
//
// For double, spec.f=52, so the unpacked fraction is 53 bits wide.  The bug
// triggers when exponent > 52, i.e. for values >= 2^53: that is the first
// binade where the hidden bit (at position 52, the top of the 53-bit fraction)
// would need to land at position 53 or higher -- one past the top -- which is
// impossible without padding.  The upper bound 2^54 keeps the test in a single
// binade (all values there have exponent=53) so the analysis is clean.
//
// Every double in [2^53, 2^54) is an integer >= 2^53, so the assertion below
// holds for every concrete input, on both back-ends.

void main(void)
{
  double f;

  // [2^53, 2^54): first binade where exponent (53) > spec.f (52)
  __CPROVER_assume(f >= 9007199254740992.0); // 2^53
  __CPROVER_assume(f < 18014398509481984.0); // 2^54

  uint64_t u = (uint64_t)f;

  // The converted value must keep its magnitude.
  __CPROVER_assert(u >= 9007199254740992ULL, "u >= 2^53");
}
