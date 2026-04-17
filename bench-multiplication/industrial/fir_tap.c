#include <stdint.h>
// Q15 fixed-point multiplication (common in DSP)
int16_t q15_mul(int16_t a, int16_t b) {
  int32_t result = (int32_t)a * (int32_t)b;
  return (int16_t)(result >> 15);
}
int main() {
  int16_t x, h;
  // Commutativity of Q15 multiplication
  __CPROVER_assert(q15_mul(x, h) == q15_mul(h, x), "Q15 comm");
}
