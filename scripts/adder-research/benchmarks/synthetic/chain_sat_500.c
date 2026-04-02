// SAT: chained additions a+b+c+d
#define N 500
int main() {
  int a[N], b[N], c[N], d[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i]+b[i]+c[i]+d[i] != 0, "");
}
