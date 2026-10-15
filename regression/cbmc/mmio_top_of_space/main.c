int main()
{
  // Region ending exactly at 2^64 spans the top of the address space.
  volatile unsigned char *p = (volatile unsigned char *)0xFFFFFFFFFFFFFFFFULL;
  *p = 0x42;
  __CPROVER_assert(*p == 0x42, "top-of-address-space MMIO read-back");
  return 0;
}
