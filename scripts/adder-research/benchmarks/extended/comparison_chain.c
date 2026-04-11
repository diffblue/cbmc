#include <stdint.h>
#define N 150
int main() {
  int32_t arr[N];
  // Bubble sort verification: check if sorted
  for(int i = 0; i < N-1; i++)
    __CPROVER_assume(arr[i] <= arr[i+1]);
  // Verify transitivity
  __CPROVER_assert(arr[0] <= arr[N-1], "");
}
