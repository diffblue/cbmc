#include <stdint.h>
int main() {
  uint16_t base, modulus;
  __CPROVER_assume(modulus > 1);
  // Square-and-multiply: base^2 mod m
  uint32_t wide = (uint32_t)base * (uint32_t)base;
  uint16_t squared = (uint16_t)(wide % modulus);
  // Verify: squared < modulus
  __CPROVER_assert(squared < modulus, "mod reduction");
}
