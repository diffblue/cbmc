#include <stdint.h>
// Compiler optimization: x/10 ≈ (x * 0xCCCCCCCD) >> 35
int main() {
  uint32_t x;
  __CPROVER_assume(x <= 1000000);
  uint32_t div_result = x / 10;
  uint64_t approx = ((uint64_t)x * 0xCCCCCCCDULL) >> 35;
  __CPROVER_assert(div_result == (uint32_t)approx, "div by const");
}
