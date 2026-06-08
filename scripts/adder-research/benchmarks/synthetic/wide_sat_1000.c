// SAT: 64-bit addition
#define N 1000
int main() {
  long long a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i] + b[i] > a[i], "");
}
