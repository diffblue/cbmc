int main()
{
  // A 32-bit MMIO store must update all four bytes rather than truncating to
  // a single byte, and a 32-bit load must read all four back.
  volatile unsigned int *w = (volatile unsigned int *)0x1000;
  *w = 0x12345678;
  __CPROVER_assert(*w == 0x12345678, "32-bit MMIO value round-trips");

  // The store spans consecutive bytes in little-endian order.
  volatile unsigned char *b = (volatile unsigned char *)0x1000;
  __CPROVER_assert(b[0] == 0x78, "byte 0 (LSB)");
  __CPROVER_assert(b[1] == 0x56, "byte 1");
  __CPROVER_assert(b[2] == 0x34, "byte 2");
  __CPROVER_assert(b[3] == 0x12, "byte 3 (MSB)");
  return 0;
}
