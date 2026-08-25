// The mirror image of overflow-result-flattening1: a genuine overflow must
// still be reported.  If the flattened overflow_result_exprt struct is read
// back with the fields swapped, the overflow flag becomes the top bit of the
// truncated result, and the result becomes (result << 1) | overflow_flag.
//
// The operands are constrained to a range rather than to a single value so
// that the multiplication survives constant propagation and actually reaches
// the SMT2 back-end.

unsigned int prod;

int main(void)
{
  unsigned int a, b;
  __CPROVER_assume(a >= 0x10000u && a <= 0x10001u);
  __CPROVER_assume(b >= 0x10000u && b <= 0x10001u);

  // a * b lies in [2^32, (2^16+1)^2], so it always overflows an unsigned int,
  // and for a == b == 0x10000 the truncated product is exactly 0.  Bit 31 of
  // the truncated product is 0 for every allowed pair, so a back-end that
  // reads the overflow flag from there misses the overflow entirely.
  int overflow = __builtin_mul_overflow(a, b, &prod);
  __CPROVER_assert(!overflow, "expected to FAIL: the product always overflows");
  __CPROVER_assert(prod != 0, "expected to FAIL: truncated product can be 0");

  return 0;
}
