int main()
{
  int a[5];
  int b[5];

  a[0]=0;
  a[1]=1;
  a[2]=2;
  a[3]=3;
  a[4]=4;

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<5) ==> b[i]==a[i]});
  // clang-format on

  assert(b[0]==0);
  assert(b[1]==1);
  assert(b[2]==2);
  assert(b[3]==3);
  assert(b[4]==4);
  return 0;
}
