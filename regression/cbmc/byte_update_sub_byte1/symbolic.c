int main()
{
  unsigned x;
  unsigned offset;
  __CPROVER_assume(offset == 0);
  __CPROVER_bitvector[1] *p = (__CPROVER_bitvector[1] *)((char *)&x + offset);
  *p = 0;
  __CPROVER_assert((x & 0x80u) == 0u, "MSB of byte 0 is cleared");
}
