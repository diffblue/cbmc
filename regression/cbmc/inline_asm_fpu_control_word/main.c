int main(void)
{
  unsigned short old, new = 3 << 10;

  // fldcw uses its own operand (%1), not the first operand of the statement
  asm volatile("fstcw %0; fldcw %1" : "=m"(old) : "m"(new));
  __CPROVER_assert((old >> 10 & 3) == 0, "initial rounding mode");

  asm volatile("fstcw %0" : "=m"(old));
  __CPROVER_assert((old >> 10 & 3) == 3, "rounding mode set by fldcw");

  return 0;
}
