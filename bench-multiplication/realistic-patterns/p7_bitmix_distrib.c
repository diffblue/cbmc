// Bit-mixing with distributivity property: (a^b) * c == a*c ^ b*c
// is FALSE in general, but a*(b+c) == a*b + a*c IS true.
// We test the latter with stored intermediates.
#include <stdint.h>
uint64_t opaque(uint64_t x) { return x; }
int main() {
  uint16_t a, b, c;
  uint64_t va=a, vb=b, vc=c;
  uint64_t bc = opaque(vb + vc);
  uint64_t lhs = opaque(va * bc);
  uint64_t rhs = opaque(va * vb) + opaque(va * vc);
  __CPROVER_assert(lhs == rhs, "bitmix distributivity");
  return 0;
}
