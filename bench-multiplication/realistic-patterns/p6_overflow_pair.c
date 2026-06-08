// Overflow check on a multiplication should be commutative.
// Common in numerical code with overflow guards.
#include <stdint.h>
int overflows_u32(uint32_t a, uint32_t b) {
  uint64_t p = (uint64_t)a * (uint64_t)b;
  return (p >> 32) != 0;
}
int overflows_u32_swapped(uint32_t a, uint32_t b) {
  uint64_t p = (uint64_t)b * (uint64_t)a;
  return (p >> 32) != 0;
}
int main() {
  uint16_t a, b;
  __CPROVER_assert(overflows_u32(a, b) == overflows_u32_swapped(a, b),
                   "overflow check commutativity");
  return 0;
}
