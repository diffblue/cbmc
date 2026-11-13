// As multibyte.c, but with a symbolic (constrained-to-0) byte offset so that
// the variable-offset branch of convert_byte_update is exercised for a
// non-byte-aligned update wider than one byte.
int main()
{
  unsigned x = 0xFFFFFFFFu;
  unsigned offset;
  __CPROVER_assume(offset == 0);
  __CPROVER_bitvector[9] *p = (__CPROVER_bitvector[9] *)((char *)&x + offset);
  *p = 0;
  __CPROVER_assert(x == 0xFFFF007Fu, "9-bit update matches lower_byte_update");
  return 0;
}
