#include <stdint.h>
#include <limits.h>
#define N 200
int main() {
  int32_t vals[N];
  uint32_t sum_abs = 0;
  for(int i = 0; i < N; i++) {
    __CPROVER_assume(vals[i] != INT_MIN);
    int32_t abs_val = (vals[i] < 0) ? -vals[i] : vals[i];
    sum_abs += (uint32_t)abs_val;
  }
  __CPROVER_assert(sum_abs < 0xFFFFFFFF, "");
}
