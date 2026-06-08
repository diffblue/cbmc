// CRC-style chained multiplications by a constant: should always
// produce the same result for the same input.
#include <stdint.h>
uint32_t step(uint32_t s, uint32_t v) {
  return (s ^ v) * 0x9e3779b9u;  // golden ratio multiplier
}
uint32_t hash3(uint32_t a, uint32_t b, uint32_t c) {
  return step(step(step(0, a), b), c);
}
int main() {
  uint16_t a, b, c;
  uint32_t va = a, vb = b, vc = c;
  // Same arguments via two distinct call sites should give same hash.
  uint32_t h1 = hash3(va, vb, vc);
  uint32_t h2 = hash3(va, vb, vc);
  __CPROVER_assert(h1 == h2, "crc chain determinism");
  return 0;
}
