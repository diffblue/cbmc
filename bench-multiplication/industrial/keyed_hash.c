#include <stdint.h>
uint16_t keyed_hash(uint16_t key, uint16_t data) {
  uint16_t h = key ^ data;
  h *= 0x9e37;
  h ^= h >> 8;
  h *= 0x9e37;
  h ^= h >> 8;
  return h;
}
int main() {
  uint16_t key, data;
  __CPROVER_assert(keyed_hash(key, data) == keyed_hash(key, data), "deterministic");
}
