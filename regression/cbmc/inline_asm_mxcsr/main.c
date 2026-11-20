int main(void)
{
  unsigned csr;

  // the rounding mode is bits 13 and 14 of the SSE control register
  asm volatile("stmxcsr %0" : "=m"(csr));
  __CPROVER_assert((csr >> 13 & 3) == 0, "initial rounding mode");

  // round downwards
  csr = (csr & ~0x6000u) | 0x2000u;
  asm volatile("ldmxcsr %0" : : "m"(csr));
  float f = 1.0f;
  __CPROVER_assert(f / 3.0f == 0x1.555554p-2f, "rounded downwards");

  unsigned again;
  asm volatile("stmxcsr %0" : "=m"(again));
  __CPROVER_assert((again >> 13 & 3) == 1, "rounding mode set by ldmxcsr");

  // the other bits are not modeled
  __CPROVER_assert(again == csr, "other bits"); // fails

  return 0;
}
