#include <stdint.h>
#define N 100
int main() {
  uint8_t vals[N];
  uint8_t sum = 0;
  for(int i = 0; i < N; i++) {
    uint16_t tmp = (uint16_t)sum + vals[i];
    sum = (tmp > 255) ? 255 : (uint8_t)tmp;
  }
  __CPROVER_assert(sum <= 255, "");
}
