int main()
{
  int a[10], b[10];
  int x;
  unsigned y,z;
  __CPROVER_assume(2<=y && y<=4);
  __CPROVER_assume(6<=z && z<=8);
  b[y] = x;
  b[z] = x;
  for(unsigned i = 0;i<10;i++) {
    a[i] = b[i];
  }
  assert(a[y]==a[z]);
}
