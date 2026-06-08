#include <stdint.h>
#define N 100
int main() {
  uint32_t x, result = 0;
  for(int i = 0; i < N; i++) {
    result += x;
    x <<= 1;
  }
  __CPROVER_assert(result != 0xDEADBEEF, "");
}
