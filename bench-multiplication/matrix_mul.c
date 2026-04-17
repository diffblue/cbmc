#include <stdint.h>
int main() {
  uint8_t a00, a01, a10, a11;
  uint8_t b00, b01, b10, b11;
  // C = A * B
  uint8_t c00 = a00*b00 + a01*b10;
  uint8_t c01 = a00*b01 + a01*b11;
  uint8_t c10 = a10*b00 + a11*b10;
  uint8_t c11 = a10*b01 + a11*b11;
  // D = B * A
  uint8_t d00 = b00*a00 + b01*a10;
  uint8_t d01 = b00*a01 + b01*a11;
  uint8_t d10 = b10*a00 + b11*a10;
  uint8_t d11 = b10*a01 + b11*a11;
  // Matrix multiplication is NOT commutative in general
  // But the trace (sum of diagonal) IS invariant: tr(AB) == tr(BA)
  __CPROVER_assert((uint8_t)(c00 + c11) == (uint8_t)(d00 + d11), "trace invariant");
}
