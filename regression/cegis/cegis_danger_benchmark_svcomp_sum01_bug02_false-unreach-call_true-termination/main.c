#define a (2)
int main() {
  int i;
  int j=10;
  int n;
  int sn=0;

  for(i=1; i<=n; i++) {
    if (i<j)
    sn = sn + a;
    j--;
  }

  __CPROVER_assert(sn==n*a || sn == 0, "A");
  return 0;
}
