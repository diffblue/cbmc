// Naive a*x*x + b*x + c vs a partially-stored equivalent.
#include <stdint.h>
uint64_t store(uint64_t x) { return x; }
int main() {
  uint16_t a, b, c, x;
  uint64_t va=a, vb=b, vc=c, vx=x;
  // Naive: a*x*x + b*x + c, computed left-to-right.
  uint64_t lhs = store(store(va * vx) * vx) + store(vb * vx) + vc;
  // Equivalent via different order of partial mult.
  uint64_t rhs = store(vx * store(va * vx)) + store(vx * vb) + vc;
  __CPROVER_assert(lhs == rhs, "polynomial evaluation reorder");
  return 0;
}
