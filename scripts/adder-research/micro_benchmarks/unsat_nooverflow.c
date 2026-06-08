// UNSAT: constrained so overflow is impossible
#include <limits.h>
#define N 200
int main() {
  int a[N], b[N];
  for(int i = 0; i < N; ++i) {
    __CPROVER_assert(
      b[i] <= 0 ||
      (a[i] >= (INT_MAX >> 28) || b[i] >= (INT_MAX >> 28)) ||
      (a[i] <= (INT_MIN >> 1) || b[i] <= (INT_MIN >> 1)) ||
      a[i] + b[i] > a[i], "");
  }
}
