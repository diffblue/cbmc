// Cryptographic modular multiplication should be commutative.
// Pattern: a*b mod m == b*a mod m, common in RSA/elliptic-curve code.
#include <stdint.h>
uint64_t store(uint64_t x) { return x; }
int main() {
  uint16_t a, b;
  __CPROVER_assume(a > 0 && b > 0);
  const uint64_t m = 1000000007ULL;
  uint64_t r1 = store(((uint64_t)a * (uint64_t)b) % m);
  uint64_t r2 = store(((uint64_t)b * (uint64_t)a) % m);
  __CPROVER_assert(r1 == r2, "modmul commutativity");
  return 0;
}
