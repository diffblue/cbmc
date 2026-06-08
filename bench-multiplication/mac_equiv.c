#include <stdint.h>
int main() {
  uint8_t a[4], b[4];
  // Two ways to compute dot product:
  uint8_t sum1 = (uint8_t)(a[0]*b[0]) + (uint8_t)(a[1]*b[1]) + 
                 (uint8_t)(a[2]*b[2]) + (uint8_t)(a[3]*b[3]);
  uint8_t sum2 = (uint8_t)(b[0]*a[0]) + (uint8_t)(b[1]*a[1]) + 
                 (uint8_t)(b[2]*a[2]) + (uint8_t)(b[3]*a[3]);
  __CPROVER_assert(sum1 == sum2, "MAC comm");
}
