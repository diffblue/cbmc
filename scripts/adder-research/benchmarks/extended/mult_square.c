#include <stdint.h>
int main() {
  uint32_t a, b;
  __CPROVER_assume(a < 65536 && b < 65536);
  uint32_t prod = a * b;
  uint32_t sum = a + b;
  __CPROVER_assert(prod <= sum * sum, "");
}
