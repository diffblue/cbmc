#include <stdint.h>
int32_t poly_hash(uint8_t *data, int len) {
  int32_t h = 0;
  for(int i = 0; i < len; i++)
    h = h * 31 + data[i];
  return h;
}
int main() {
  uint8_t data[4];
  int32_t h1 = poly_hash(data, 4);
  int32_t h2 = poly_hash(data, 4);
  __CPROVER_assert(h1 == h2, "deterministic");
}
