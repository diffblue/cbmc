// Two equivalent index computations through different code paths.
// Common in image-processing verification.
#include <stdint.h>
uint64_t store(uint64_t x) { return x; }
int main() {
  uint16_t row, col, height, width;
  __CPROVER_assume(row < 200 && col < 200 && height >= 1 && width >= 1);
  uint64_t idx1 = store((uint64_t)row * (uint64_t)width + (uint64_t)col);
  uint64_t idx2 = store((uint64_t)col + (uint64_t)width * (uint64_t)row);
  __CPROVER_assert(idx1 == idx2, "pixel index commutativity");
  return 0;
}
