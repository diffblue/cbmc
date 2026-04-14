// Non-byte-aligned sub-byte updates whose width exceeds the byte width. These
// are the cases where placing only the trailing partial byte (rather than
// shifting the whole value) diverges from lower_byte_update. Writing a zero of
// the given width over 0xFFFFFFFF must clear the value's bits at the high end
// of the last partial byte, i.e. bit positions [tail_shift, tail_shift+width).
int main()
{
  // 9-bit zero: tail_shift = 8 - (9 % 8) = 7, so bits [7, 16) are cleared.
  unsigned x9 = 0xFFFFFFFFu;
  __CPROVER_bitvector[9] *p9 = (__CPROVER_bitvector[9] *)&x9;
  *p9 = 0;
  __CPROVER_assert(x9 == 0xFFFF007Fu, "9-bit update matches lower_byte_update");

  // 17-bit zero: tail_shift = 8 - (17 % 8) = 7, so bits [7, 24) are cleared.
  unsigned x17 = 0xFFFFFFFFu;
  __CPROVER_bitvector[17] *p17 = (__CPROVER_bitvector[17] *)&x17;
  *p17 = 0;
  __CPROVER_assert(
    x17 == 0xFF00007Fu, "17-bit update matches lower_byte_update");

  return 0;
}
