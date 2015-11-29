int main()
{
  int a[5], b[5];
  int x,z;
  unsigned y;
  __CPROVER_assume(2<=y && y<=3);
  for(unsigned i = 0;i<5;i++) {
    a[i] = b[i];
    if(z) a[y] = x;
    assert(a[i]==b[i] || a[i]==x);
  }
}
