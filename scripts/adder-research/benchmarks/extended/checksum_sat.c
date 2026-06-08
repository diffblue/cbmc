#include <stdint.h>
#define N 80
int main() {
  uint32_t data[N], sum = 0;
  for(int i = 0; i < N; i++)
    sum += data[i];
  __CPROVER_assert(sum != 0xDEADBEEF, "");
}
