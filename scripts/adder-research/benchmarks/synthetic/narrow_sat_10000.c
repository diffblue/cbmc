// SAT: 8-bit addition (many small adders)
#define N 10000
int main() {
  unsigned char a[N], b[N];
  for(int i=0; i<N; ++i)
    __CPROVER_assert((unsigned char)(a[i]+b[i]) >= a[i], "");
}
