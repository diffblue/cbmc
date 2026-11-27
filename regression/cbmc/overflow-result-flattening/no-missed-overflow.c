// The mirror image of no-spurious-failure.c: a genuine overflow must still
// be reported.  If the flattened overflow_result_exprt struct is read
// back with the fields swapped, the overflow flag becomes the top bit of the
// truncated result, and the result becomes (result << 1) | overflow_flag.
//
// The operands are constrained to a range rather than to a single value so
// that the operations survive constant propagation and actually reach the
// SMT2 back-end.  For each operation below, every allowed pair of operands
// overflows, and bit 31 of the truncated result is 0, so a back-end that reads
// the overflow flag from there misses the overflow entirely.

unsigned int prod, usum, udiff;
signed int sprod, ssum, sdiff;

int main(void)
{
  unsigned int a, b;
  __CPROVER_assume(a >= 0x10000u && a <= 0x10001u);
  __CPROVER_assume(b >= 0x10000u && b <= 0x10001u);

  // a * b lies in [2^32, (2^16+1)^2], and for a == b == 0x10000 the truncated
  // product is exactly 0.
  int overflow = __builtin_mul_overflow(a, b, &prod);
  __CPROVER_assert(!overflow, "expected to FAIL: the product always overflows");
  __CPROVER_assert(prod != 0, "expected to FAIL: truncated product can be 0");

  // The signed variants use separate emitters in the SMT2 back-end.
  signed int sa, sb;
  __CPROVER_assume(sa >= 0x10000 && sa <= 0x10001);
  __CPROVER_assume(sb >= 0x10000 && sb <= 0x10001);

  // sa * sb > INT_MAX, and the truncated product lies in [0, 0x20001].
  int sprod_overflow = __builtin_mul_overflow(sa, sb, &sprod);
  __CPROVER_assert(
    !sprod_overflow, "expected to FAIL: the signed product always overflows");

  signed int sc, sd;
  __CPROVER_assume(sc >= -0x7fffffff - 1 && sc <= -0x7fffffff);
  __CPROVER_assume(sd >= -0x7fffffff - 1 && sd <= -0x7fffffff);

  // sc + sd < INT_MIN, and the truncated sum lies in [0, 2].
  int ssum_overflow = __builtin_add_overflow(sc, sd, &ssum);
  __CPROVER_assert(
    !ssum_overflow, "expected to FAIL: the signed sum always overflows");

  signed int se;
  __CPROVER_assume(se >= 2 && se <= 3);

  // sc - se < INT_MIN, and the truncated difference lies in
  // [0x7ffffffd, 0x7fffffff].
  int sdiff_overflow = __builtin_sub_overflow(sc, se, &sdiff);
  __CPROVER_assert(
    !sdiff_overflow,
    "expected to FAIL: the signed difference always overflows");

  // The unsigned plus/minus emitter uses the (width+1)-bit sum, whose top bit
  // is the carry, as the flattened struct rather than a concatenation. Check it
  // in the same way, so that no future change to it can swap the fields.
  unsigned int ua, ub;
  __CPROVER_assume(ua >= 0x80000000u && ua <= 0x80000001u);
  __CPROVER_assume(ub >= 0x80000000u && ub <= 0x80000001u);

  // ua + ub >= 2^32, and the truncated sum lies in [0, 2].
  int usum_overflow = __builtin_add_overflow(ua, ub, &usum);
  __CPROVER_assert(
    !usum_overflow, "expected to FAIL: the unsigned sum always overflows");

  unsigned int uc, ud;
  __CPROVER_assume(uc <= 1u);
  __CPROVER_assume(ud >= 0x80000002u && ud <= 0x80000003u);

  // uc - ud < 0, and the truncated difference lies in
  // [0x7ffffffd, 0x7fffffff].
  int udiff_overflow = __builtin_sub_overflow(uc, ud, &udiff);
  __CPROVER_assert(
    !udiff_overflow,
    "expected to FAIL: the unsigned difference always overflows");

  return 0;
}
