#include <stdint.h>
int main() {
  uint16_t a00, a01, a10, a11;
  uint16_t b00, b01, b10, b11;
  uint16_t c00 = a00*b00 + a01*b10;
  uint16_t c01 = a00*b01 + a01*b11;
  uint16_t c10 = a10*b00 + a11*b10;
  uint16_t c11 = a10*b01 + a11*b11;
  uint16_t d00 = b00*a00 + b01*a10;
  uint16_t d01 = b00*a01 + b01*a11;
  uint16_t d10 = b10*a00 + b11*a10;
  uint16_t d11 = b10*a01 + b11*a11;
  __CPROVER_assert((uint16_t)(c00 + c11) == (uint16_t)(d00 + d11), "trace invariant");
}
