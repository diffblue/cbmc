#include <stdint.h>
#define N 2000
int main() {
  int32_t arr[N];
  for(int i = 0; i < N-1; i++)
    __CPROVER_assume(arr[i] <= arr[i+1]);
  // Can first equal last? Yes (all equal)
  __CPROVER_assert(arr[0] != arr[N-1], "");
}
