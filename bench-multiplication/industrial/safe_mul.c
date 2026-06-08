#include <stdint.h>
#include <stdbool.h>
bool checked_mul_u32(uint32_t a, uint32_t b, uint32_t *result) {
  uint64_t wide = (uint64_t)a * (uint64_t)b;
  *result = (uint32_t)wide;
  return (wide >> 32) == 0; // true if no overflow
}
int main() {
  uint32_t a, b, r1, r2;
  bool ok1 = checked_mul_u32(a, b, &r1);
  bool ok2 = checked_mul_u32(b, a, &r2);
  // If both succeed, results must match
  __CPROVER_assume(ok1 && ok2);
  __CPROVER_assert(r1 == r2, "checked mul comm");
}
