int main(void)
{
  float f = 1.0f;
  char state[512] = {0};
  // fxrstor is not modeled, and may change the rounding mode
  asm volatile("fxrstor %0" : : "m"(state));
  // holds with round-to-nearest only
  __CPROVER_assert(f / 3.0f == 0x1.555556p-2f, "rounding mode");
  return 0;
}
