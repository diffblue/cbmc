int main(void)
{
  float f = 1.0f;
  unsigned csr = 0;
  // ldmxcsr is not modeled, and may change the rounding mode
  asm volatile("ldmxcsr %0" : : "m"(csr));
  // holds with round-to-nearest only
  __CPROVER_assert(f / 3.0f == 0x1.555556p-2f, "rounding mode");
  return 0;
}
