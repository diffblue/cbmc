#include <stdint.h>
#include <limits.h>
#define N 2000
int main() {
  int32_t vals[N];
  uint32_t sum = 0;
  for(int i = 0; i < N; i++) {
    __CPROVER_assume(vals[i] != INT_MIN);
    sum += (uint32_t)((vals[i] < 0) ? -vals[i] : vals[i]);
  }
  __CPROVER_assert(sum < 0xFFFFFFFF, "");
}
