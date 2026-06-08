#include <stdint.h>
int main() {
  uint16_t a, b, c, d;
  uint32_t ab = (uint32_t)a * b;
  uint32_t cd = (uint32_t)c * d;
  __CPROVER_assert(ab != cd || a == c, "");
}
