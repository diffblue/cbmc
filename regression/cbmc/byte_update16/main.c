int main()
{
  unsigned len;
  unsigned A[len];
  if(len > 1 || len == 0 || sizeof(unsigned) != 4)
    return 0;

  A[0] = 0xA5FFFFA5U;
  __CPROVER_bitvector[1] *bptr = &A[len - 1];
  *bptr = 0;
  __CPROVER_assert(A[0] == 0xA5FFFF25U || A[0] == 0x25FFFFA5U, "MSB cleared");
}
