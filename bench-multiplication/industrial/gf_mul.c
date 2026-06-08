#include <stdint.h>
// GF(2^8) multiplication used in AES
uint8_t gf_mul(uint8_t a, uint8_t b) {
  uint8_t p = 0;
  for(int i = 0; i < 8; i++) {
    if(b & 1) p ^= a;
    uint8_t hi = a & 0x80;
    a <<= 1;
    if(hi) a ^= 0x1b; // x^8 + x^4 + x^3 + x + 1
    b >>= 1;
  }
  return p;
}
int main() {
  uint8_t a, b;
  __CPROVER_assert(gf_mul(a, b) == gf_mul(b, a), "GF comm");
}
