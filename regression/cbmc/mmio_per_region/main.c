int main()
{
  volatile char *p = (volatile char *)0x1000;
  *p = 0x42;
  char val = *p;
  __CPROVER_assert(val == 0x42, "MMIO read-back");
  return 0;
}
