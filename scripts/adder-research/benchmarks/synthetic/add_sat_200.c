// SAT: a[i]+b[i] > a[i] (trivially SAT via b<0)
#define N 200
int main() {
  int a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i]+b[i] > a[i], "");
}
