#include <stdint.h>
#define N 500
int main() {
  uint16_t arr[N];
  uint32_t sum = 0;
  for(int i = 0; i < N; i++)
    sum += arr[i];
  __CPROVER_assert(sum != 12345678, "");
}
