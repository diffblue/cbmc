#define a (2)
int main() {
  int i;
  int n;
  int sn=0;

  for(i=1; i<=n; i++) {
    sn = sn + a;
    if (i==4) sn=-10;
  }

  __CPROVER_assert(sn==n*a || sn == 0, "A");

  return 0;
}
