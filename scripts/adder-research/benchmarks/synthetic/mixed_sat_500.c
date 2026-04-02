// SAT: mixed add/sub/compare
#define N 500
int main() {
  int a[N], b[N], c[N];
  for(int i=0; i<N; ++i) {
    int sum = a[i] + b[i];
    int diff = a[i] - c[i];
    __CPROVER_assert(sum != diff || b[i] == -c[i] || a[i]+b[i] != a[i]-c[i], "");
  }
}
