#include <stdint.h>
uint32_t fmix32(uint32_t h) {
  h ^= h >> 16;
  h *= 0x85ebca6b;
  h ^= h >> 13;
  h *= 0xc2b2ae35;
  h ^= h >> 16;
  return h;
}
int main() {
  uint32_t x;
  __CPROVER_assert(fmix32(x) == fmix32(x), "deterministic");
}
