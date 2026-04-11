#include <stdint.h>
#define N 20
int main() {
  uint32_t a[N], b[N], c[N], d[N];
  for(int i = 0; i < N; i++) {
    c[i] = a[i] + b[i];
    d[i] = a[i] + b[i] + 1; // different!
  }
  // Can c[0] == d[0]? Yes if carry makes them equal
  __CPROVER_assert(c[0] != d[0], "");
}
