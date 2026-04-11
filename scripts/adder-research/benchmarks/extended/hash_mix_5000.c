#include <stdint.h>
#define ROUNDS 5000
int main() {
  uint32_t a, b, c;
  for(int i = 0; i < ROUNDS; i++) {
    a -= b; a -= c; a ^= (c >> 13);
    b -= c; b -= a; b ^= (a << 8);
    c -= a; c -= b; c ^= (b >> 13);
  }
  __CPROVER_assert(a != 0x12345678 || b != 0x9abcdef0, "");
}
