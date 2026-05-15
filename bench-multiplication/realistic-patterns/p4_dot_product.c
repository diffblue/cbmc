// Three-term dot product computed in two orders.
#include <stdint.h>
uint64_t opaque(uint64_t x) { return x; }
int main() {
  uint16_t a, b, c, x, y, z;
  uint64_t s1 = opaque((uint64_t)a * (uint64_t)x)
              + opaque((uint64_t)b * (uint64_t)y)
              + opaque((uint64_t)c * (uint64_t)z);
  uint64_t s2 = opaque((uint64_t)y * (uint64_t)b)
              + opaque((uint64_t)x * (uint64_t)a)
              + opaque((uint64_t)z * (uint64_t)c);
  __CPROVER_assert(s1 == s2, "dot product reorder");
  return 0;
}
