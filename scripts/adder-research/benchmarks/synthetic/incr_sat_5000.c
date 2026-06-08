// SAT: increment by constant
#define N 5000
int main() {
  int a[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert(a[i] + 1 != a[i], "");
}
