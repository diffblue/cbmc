#include <stdint.h>
int main() {
  uint32_t a, b;
  __CPROVER_assume(b > 0 && b < 1000);
  uint32_t q = a / b;
  uint32_t r = a % b;
  __CPROVER_assert(q * b + r == a, "");
}
