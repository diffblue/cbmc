#include <stdint.h>
#define ROUNDS 500
int main() {
  uint32_t a, b, c;
  uint32_t a2 = a, b2 = b, c2 = c;
  // Run same hash on same input twice
  for(int i = 0; i < ROUNDS; i++) {
    a -= b; a -= c; a ^= (c >> 13);
    b -= c; b -= a; b ^= (a << 8);
    c -= a; c -= b; c ^= (b >> 13);
  }
  for(int i = 0; i < ROUNDS; i++) {
    a2 -= b2; a2 -= c2; a2 ^= (c2 >> 13);
    b2 -= c2; b2 -= a2; b2 ^= (a2 << 8);
    c2 -= a2; c2 -= b2; c2 ^= (b2 >> 13);
  }
  // Same input → same output (UNSAT: always true)
  __CPROVER_assert(a == a2 && b == b2 && c == c2, "");
}
