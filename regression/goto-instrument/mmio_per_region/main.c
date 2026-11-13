// Test for per-region MMIO object model

int main()
{
  // Write to MMIO region at 0x1000
  volatile char *p1 = (volatile char *)0x1000;
  *p1 = 0x42;

  // Read back and verify
  char val1 = *p1;
  __CPROVER_assert(val1 == 0x42, "MMIO read-back from region 1");

  // Write to MMIO region at 0x2000
  volatile char *p2 = (volatile char *)0x2000;
  *p2 = 0x55;

  // Read back and verify
  char val2 = *p2;
  __CPROVER_assert(val2 == 0x55, "MMIO read-back from region 2");

  // Verify regions are independent
  char val1_again = *p1;
  __CPROVER_assert(val1_again == 0x42, "region 1 unaffected by region 2 write");

  // Normal memory access still works
  char normal_var = 100;
  char *p4 = &normal_var;
  __CPROVER_assert(*p4 == 100, "normal memory access works");

  return 0;
}
