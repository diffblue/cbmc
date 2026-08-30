int main()
{
  unsigned x;
  __CPROVER_bitvector[1] *p = (__CPROVER_bitvector[1] *)&x;
  *p = 0;
  __CPROVER_assert((x & 0x80u) == 0u, "MSB of byte 0 is cleared");
}
