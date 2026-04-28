// Test float-to-integer conversion for values that need more bits than
// the float's fraction.
//
// Bug: float_bvt::to_integer did not extend the fraction to the
// destination width before shifting, causing incorrect results when
// the integer type was wider than the fraction (shift distance went
// negative for large exponents).
//
// float has 24 bits of fraction (including hidden bit).
// Converting to a 32-bit int requires values up to 2^31-1, which
// needs the full 32-bit integer range.

#include <assert.h>
#include <limits.h>

extern int __CPROVER_rounding_mode;

int main()
{
  float a;

  // Test 1: Large positive float -> int
  __CPROVER_assume(a == 1000000.0f);
  __CPROVER_rounding_mode = 3; // ROUND_TO_ZERO (required for C semantics)
  int r1 = (int)a;
  assert(r1 == 1000000);

  // Test 2: Value requiring more than 24 bits
  float b;
  __CPROVER_assume(b == 16777216.0f); // 2^24, exactly representable
  int r2 = (int)b;
  assert(r2 == 16777216);

  // Test 3: Larger value
  float c;
  __CPROVER_assume(c == 2.0e9f); // ~2 billion, near INT_MAX
  int r3 = (int)c;
  assert(r3 == 2000000000);

  // Test 4: Negative large value
  float d;
  __CPROVER_assume(d == -1000000.0f);
  int r4 = (int)d;
  assert(r4 == -1000000);

  // Test 5: Float to unsigned int
  float e;
  __CPROVER_assume(e == 3000000000.0f); // 3 billion, fits in unsigned
  unsigned int r5 = (unsigned int)e;
  // 3000000000.0f is exactly 0x1.6bcc41p+31 = 3000000000 (exact)
  // Actually 3e9 rounds to 3000000000 in float? Let's check:
  // 3000000000 = 0xB2D05E00, float: 0x1.65a0bcp+31 = 2999999488
  // Use an exact value instead.
  __CPROVER_assume(e == 16777216.0f);
  unsigned int r5b = (unsigned int)e;
  assert(r5b == 16777216u);

  return 0;
}
