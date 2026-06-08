#include <stdint.h>
int main() {
  uint32_t v;
  // Count bits naively
  int count = 0;
  uint32_t x = v;
  while(x) { count += x & 1; x >>= 1; }
  // Assert count is not 16 (SAT: many values have popcount != 16)
  __CPROVER_assert(count != 16, "");
}
