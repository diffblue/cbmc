int a[5], b[5];

int main()
{
  unsigned x;
  __CPROVER_assume(0<=x && x<=4);
  b[x] = x;
  for(unsigned i=0;i<5;i++) {
    a[i] = b[i];
  }
  assert(a[x]==b[x]);
}
