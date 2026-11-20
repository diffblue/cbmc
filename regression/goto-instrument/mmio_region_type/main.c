int main()
{
  volatile unsigned int *reg = (volatile unsigned int *)0x1000;
  *reg = 0x12345678;
  unsigned int readback = *reg;
  __CPROVER_assert(readback == 0x12345678, "value read back from the region");
  return 0;
}
