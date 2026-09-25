void *ioremap_wc(unsigned long phys, unsigned long size);

int main()
{
  volatile unsigned int *reg = (volatile unsigned int *)ioremap_wc(0x1000, 256);
  *reg = 0x12345678;
  unsigned int readback = *reg;
  __CPROVER_assert(readback == 0x12345678, "value read back from weak region");
  return 0;
}
