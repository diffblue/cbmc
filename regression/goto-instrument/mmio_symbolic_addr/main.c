// Test symbolic address dispatch over MMIO regions

int main()
{
  volatile char *p1 = (volatile char *)0x1000;
  volatile char *p2 = (volatile char *)0x2000;

  *p1 = 0x11;
  *p2 = 0x22;

  // Symbolic pointer: could be either region
  char nondet;
  volatile char *p = nondet ? p1 : p2;
  char val = *p;

  // val must be one of the two written values
  __CPROVER_assert(
    val == 0x11 || val == 0x22, "symbolic addr reads correct region");

  return 0;
}
