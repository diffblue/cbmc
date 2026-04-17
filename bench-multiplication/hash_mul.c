#include <stdint.h>
uint32_t hash(uint32_t key) {
  key = ((key >> 16) ^ key) * 0x45d9f3b;
  key = ((key >> 16) ^ key) * 0x45d9f3b;
  key = (key >> 16) ^ key;
  return key;
}
int main() {
  uint32_t a;
  uint32_t h1 = hash(a);
  uint32_t h2 = hash(a);
  __CPROVER_assert(h1 == h2, "deterministic");
}
