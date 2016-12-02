int main()
{

  int c[2][2];
  c[0][0]=0;
  c[0][1]=1;
  c[1][0]=1;
  c[1][1]=2;

  __CPROVER_assert(__CPROVER_exists { int i; (i>=0 && i<2) ==> (__CPROVER_exists{int j; (j>=0 && j<2) ==> c[i][j]>=1 && c[i][j]<=10}) }, "Exists-Exists: successful");

  __CPROVER_assert(!__CPROVER_exists { int i; (i>=0 && i<2) ==> (!__CPROVER_exists{int j; (j>=0 && j<2) ==> c[i][j]>=1 && c[i][j]<=10}) }, "NotExists-NotExists: successful");

  __CPROVER_assert(!__CPROVER_exists { int i; (i>=0 && i<2) ==> (__CPROVER_exists{int j; (j>=0 && j<2) ==> c[i][j]>=1 && c[i][j]<=10}) }, "NotExists-Exists: failed");

  __CPROVER_assert(!__CPROVER_exists { int i; (i>=0 && i<2) ==> (__CPROVER_forall{int j; (j>=0 && j<2) ==> c[i][j]>=1 && c[i][j]<=10}) }, "NotExists-Forall: failed");

  __CPROVER_assert(!__CPROVER_forall { int i; (i>=0 && i<2) ==> (__CPROVER_forall{int j; (j>=0 && j<2) ==> c[i][j]>=1 && c[i][j]<=10}) }, "NotForall-Forall: successful");

  __CPROVER_assert(!__CPROVER_forall { int i; (i>=0 && i<2) ==> (!__CPROVER_forall{int j; (j>=0 && j<2) ==> c[i][j]>=1 && c[i][j]<=10}) }, "NotForall-NotForall: successful");

  return 0;
}
