#include <stdint.h>
#define N 500
int main() {
  uint32_t a[N], b[N], c[N];
  uint32_t carry = 0;
  for(int i = 0; i < N; i++) {
    uint64_t sum = (uint64_t)a[i] + b[i] + carry;
    c[i] = (uint32_t)sum;
    carry = (uint32_t)(sum >> 32);
  }
  __CPROVER_assume(a[0] == b[0]);
  __CPROVER_assert((c[0] & 1) == 0, "");
}
