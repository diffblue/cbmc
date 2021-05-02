int main()
{
  int a[4], b[4];
  int x, y, z;
  __CPROVER_assume(1 <= y && y <= 3);
  __CPROVER_assume(0 <= z && z <= 2);
  b[y] = x;
  b[z] = x;
  for(unsigned i = 0; i < 4; i++)
  {
    a[i] = b[i];
  }
  __CPROVER_assert(a[y] == a[z], "a[y]==a[z]");
}
