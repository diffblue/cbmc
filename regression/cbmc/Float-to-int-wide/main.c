// Test float-to-integer (and double-to-integer) conversion for values
// that need more bits than the source's fraction width.
//
// Bug: float_bvt::to_integer (SMT2 bit-blasting) and float_utilst::to_integer
// (SAT/boolbv) did not extend the unpacked fraction to the destination width
// before right-shifting to extract the integer part. The shift places the
// hidden bit at bit position `exponent` via a right shift by
// (shift_width - 1 - exponent); without padding, shift_width is only the
// spec.f+1-bit fraction width, so once the exponent exceeds spec.f the
// distance goes negative (wraps to a huge unsigned shift), the hidden bit is
// shifted off the bottom, and the conversion yields 0.
//
// Bit-level walkthrough (tiny spec.f = 3, i.e. a 4-bit fraction, dest_width
// = 8) for 16.0 = 1.000 * 2^4 (exponent 4 > spec.f 3 -- the same boundary as
// 2^53 is for double):
//   without the fix: fraction 1000, hidden bit at position 3,
//     distance = (4 - 1) - 4 = -1 -> huge unsigned shift -> 1000 >> huge = 0
//   with the fix:    pad to 1000 0000, hidden bit at position 7,
//     distance = (8 - 1) - 4 = 3  -> 1000 0000 >> 3 = 0001 0000 = 16
//
// For double (spec.f = 52) the first failing binade is [2^53, 2^54); float
// (24 fraction bits incl. hidden) is affected for any 32-bit-or-wider integer
// destination. A second, related defect -- the shift distance was computed in
// a type only as wide as the exponent -- additionally broke narrow sources
// such as _Float16 for wide destinations. Both back-ends and both defects are
// exercised below.
//
// The bit-level walkthrough is adapted from PR diffblue/cbmc#9034.

#include <assert.h>

extern int __CPROVER_rounding_mode;

int main()
{
  // Test 1: large positive float -> int.
  float a;
  __CPROVER_assume(a == 1000000.0f);
  __CPROVER_rounding_mode = 3; // ROUND_TO_ZERO (required for C semantics)
  int r1 = (int)a;
  assert(r1 == 1000000);

  // Test 2: value at fraction-width boundary (2^24, exactly representable).
  float b;
  __CPROVER_assume(b == 16777216.0f);
  int r2 = (int)b;
  assert(r2 == 16777216);

  // Test 3: value near INT_MAX, well past the fraction width.
  float c;
  __CPROVER_assume(c == 2.0e9f);
  int r3 = (int)c;
  assert(r3 == 2000000000);

  // Test 4: negative large value.
  float d;
  __CPROVER_assume(d == -1000000.0f);
  int r4 = (int)d;
  assert(r4 == -1000000);

  // Test 5: float -> unsigned int, exact value with exponent > fraction
  // width.
  float e1;
  __CPROVER_assume(e1 == 16777216.0f); // 2^24, exactly representable
  unsigned int r5 = (unsigned int)e1;
  assert(r5 == 16777216u);

  // Test 6: float -> unsigned int, value at 2^31 (exactly representable
  // as float, above INT_MAX so the unsigned-vs-signed branch matters).
  float e2;
  __CPROVER_assume(e2 == (float)(1U << 31));
  unsigned int r6 = (unsigned int)e2;
  assert(r6 == (1U << 31));

  // Test 7: float -> long long. dest_width = 64, fraction_width = 24,
  // so the fix's extension path is exercised.
  float ll1;
  __CPROVER_assume(ll1 == (float)(1LL << 30));
  long long r7 = (long long)ll1;
  assert(r7 == (1LL << 30));

  // Test 8: double -> long long. dest_width = 64, fraction_width = 53,
  // exercises a different effective_width than tests 7.
  double d1;
  __CPROVER_assume(d1 == (double)(1LL << 40));
  long long r8 = (long long)d1;
  assert(r8 == (1LL << 40));

  // Test 9: double -> long long, value above 2^53 where double can no
  // longer represent every integer; check an exactly-representable one.
  double d2;
  __CPROVER_assume(d2 == (double)(1LL << 60));
  long long r9 = (long long)d2;
  assert(r9 == (1LL << 60));

  // Test 9b: double -> long long at the *first* failing binade, 2^53.
  // 2^53 = 1.0 * 2^53 has exponent 53 = spec.f + 1 (spec.f = 52): the hidden
  // bit, at the top of the 53-bit unpacked fraction, must move one position
  // beyond it, which is impossible without padding the fraction up to
  // dest_width first. This is the precise boundary the SMT2 back-end got
  // wrong (returning 0).
  double d3;
  __CPROVER_assume(d3 == 9007199254740992.0); // 2^53
  long long r9b = (long long)d3;
  assert(r9b == (1LL << 53));

#if defined(__SIZEOF_INT128__)
  // Test 10: float -> __int128. dest_width = 128 sits at the documented
  // boundary `(1 << (spec.e - 1)) = 128` for single-precision sources
  // (PRECONDITION in float_bvt::to_integer / float_utilst::to_integer),
  // so this exercises the widest currently-supported destination.
  float fi128;
  __CPROVER_assume(fi128 == (float)(1LL << 30));
  __int128 r10 = (__int128)fi128;
  assert(r10 == (__int128)(1LL << 30));

  // Test 11: double -> __int128. dest_width = 128, well within the
  // double precondition boundary `(1 << 10) = 1024`.
  double di128;
  __CPROVER_assume(di128 == (double)(1LL << 60));
  __int128 r11 = (__int128)di128;
  assert(r11 == (__int128)(1LL << 60));
#endif

#if defined(__FLT16_MANT_DIG__)
  // Tests 12-14: narrow source (_Float16, spec.e = 5, fraction width 11) to
  // wider integer destinations. dest_width far exceeds the source fraction,
  // so the shift distance must be built in a type wide enough to hold
  // `dest_width - 1`. Before the distance type was widened these were either
  // silently wrong (long long / __int128) or rejected outright.
  _Float16 h1;
  __CPROVER_assume(h1 == (_Float16)2048); // 2^11, exactly representable
  int r12 = (int)h1;
  assert(r12 == 2048);

  _Float16 h2;
  __CPROVER_assume(h2 == (_Float16)4096); // 2^12, exactly representable
  long long r13 = (long long)h2;
  assert(r13 == 4096);

#  if defined(__SIZEOF_INT128__)
  _Float16 h3;
  __CPROVER_assume(h3 == (_Float16)32768); // 2^15, exactly representable
  __int128 r14 = (__int128)h3;
  assert(r14 == (__int128)32768);
#  endif
#endif

  return 0;
}
