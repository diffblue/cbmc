// Test division with a subnormal dividend.
//
// Bug: float_utilst and float_bvt used an insufficient division width,
// causing 1-ULP errors when the unpacked dividend had many leading zeros
// (which happens for subnormal operands).  After the rounder's
// normalization shift left-shifts the quotient to place the leading 1 at
// the top of the buffer, the bits below the round position were all zero,
// so the `have_remainder` sticky bit was effectively lost: a true
// round-up (round=1, sticky=1) was mistaken for a tie (round=1, sticky=0)
// and broken to even.  The error only surfaces when the quotient lands
// back in the normal range and needs rounding, i.e. for subnormal/subnormal
// division; a subnormal divided by a normal yields an (exact) subnormal or
// zero and does not trigger it.

#include <assert.h>
#include <float.h>

int main()
{
  // Smallest positive subnormal divided by three times the smallest
  // subnormal: mathematically 1/3, whose IEEE-754 round-to-nearest-even
  // value is 0x1.555556p-2.  The buggy build returned 0x1.555554p-2
  // (1 ULP low) because the sticky bit was lost.
  float a, b;
  __CPROVER_assume(a == 0x1p-149f);
  __CPROVER_assume(b == 0x3p-149f);
  float r = a / b;
  assert(r == 0x1.555556p-2f);

  // A second subnormal/subnormal case, 7/4 = 1.75 exactly.
  float c, d;
  __CPROVER_assume(c == 0x7p-149f);
  __CPROVER_assume(d == 0x4p-149f);
  float r2 = c / d;
  assert(r2 == 0x1.cp+0f);

  // Exact subnormal/normal sanity check: FLT_MIN is the smallest positive
  // normal float; FLT_MIN * 0.5f is subnormal, and dividing it by 2 stays
  // exactly representable.
  float e, f;
  __CPROVER_assume(e == FLT_MIN * 0.5f);
  __CPROVER_assume(f == 2.0f);
  float r3 = e / f;
  assert(r3 == FLT_MIN * 0.25f);

  return 0;
}
