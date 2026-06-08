#include <stdint.h>
int main() {
  uint16_t a, b, c, d, e;
  uint32_t r1 = (uint32_t)a * b + (uint32_t)c * d;
  uint32_t r2 = (uint32_t)a * d + (uint32_t)c * b;
  __CPROVER_assert(r1 != r2 || (a == c && b == d) || (a == c), "");
}
