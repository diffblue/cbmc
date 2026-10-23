// Test access at offsets within an MMIO region

int main()
{
  volatile char *base = (volatile char *)0x1000;

  // Write to different offsets
  base[0] = 0xAA;
  base[10] = 0xBB;
  base[255] = 0xCC;

  // Read back via intermediate variables
  char v0 = base[0];
  char v10 = base[10];
  char v255 = base[255];

  __CPROVER_assert(v0 == (char)0xAA, "offset 0");
  __CPROVER_assert(v10 == (char)0xBB, "offset 10");
  __CPROVER_assert(v255 == (char)0xCC, "offset 255");

  // Verify independence of offsets
  char v0_again = base[0];
  __CPROVER_assert(v0_again == (char)0xAA, "offset 0 unchanged");

  return 0;
}
