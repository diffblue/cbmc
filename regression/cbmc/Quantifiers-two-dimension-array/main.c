int main()
{
  int a[2][2];
  int b[2][2];

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<2) ==> (__CPROVER_forall{int j; (j>=0 && j<2) ==> a[i][j]==i+j}) });
  __CPROVER_assume(__CPROVER_exists { int i; (i>=0 && i<2) ==> (__CPROVER_exists{int j; (j>=0 && j<2) ==> b[i][j]==i+j+1}) });
  // clang-format on

  assert(a[0][0]==0);
  assert(a[0][1]==1);
  assert(a[1][0]==1);
  assert(a[1][1]==2);
  assert(b[0][0]==1 || b[0][1]==2 || b[1][0]==2 || b[1][1]==3);
  return 0;
}
