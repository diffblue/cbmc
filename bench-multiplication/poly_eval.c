#include <stdint.h>
int main() {
  uint8_t x;
  // p(x) = 3x^2 + 5x + 7
  // Horner: ((3*x) + 5) * x + 7
  uint8_t horner = ((uint8_t)(3*x) + 5) * x + 7;
  // Direct: 3*x*x + 5*x + 7
  uint8_t direct = (uint8_t)(3 * (uint8_t)(x*x)) + (uint8_t)(5*x) + 7;
  __CPROVER_assert(horner == direct, "Horner == direct");
}
