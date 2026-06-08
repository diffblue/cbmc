// UNSAT: addition equivalence (hard for both solvers)
#define N 100
int main() {
  unsigned a[N], b[N];
  for(int i = 0; i < N; ++i) {
    unsigned sum1 = a[i] + b[i];
    unsigned sum2 = (a[i] ^ b[i]) + 2 * (a[i] & b[i]);
    __CPROVER_assert(sum1 == sum2, "");
  }
}
