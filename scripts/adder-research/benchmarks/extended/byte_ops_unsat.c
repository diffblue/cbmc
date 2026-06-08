#include <stdint.h>
#define N 20
int main() {
  uint8_t a[N], b[N], c[N], d[N];
  for(int i = 0; i < N; i++) {
    c[i] = a[i] ^ b[i];
    d[i] = a[i] ^ b[i];
  }
  int eq = 1;
  for(int i = 0; i < N; i++)
    if(c[i] != d[i]) eq = 0;
  __CPROVER_assert(eq, "");
}
