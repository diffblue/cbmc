#include <stdint.h>
int main() {
  uint16_t a, b;
  // Two ways to compute wide product:
  uint32_t wide1 = (uint32_t)a * (uint32_t)b;
  uint32_t wide2 = (uint32_t)b * (uint32_t)a;
  __CPROVER_assert(wide1 == wide2, "wide mul comm");
}
