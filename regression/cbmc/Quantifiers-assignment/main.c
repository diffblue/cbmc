int main()
{
  int a[2];
  a[0]=1;
  a[1]=2;

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  int x=__CPROVER_forall { int i; (i>=0 && i<2) ==> a[i]>=1 && a[i]<=10 };
  int y=__CPROVER_forall { int i; (i>=0 && i<2) ==> a[i]>=1 && a[i]<2 };
  int z1=__CPROVER_exists { int i; (i>=0 && i<2) ==> a[i]>=1 && a[i]<1.5 };
  int z2=__CPROVER_exists { int i; (i>=0 && i<2) ==> a[i]>=1 && a[i]<2*10 };
  // clang-format on

  assert(x);
  assert(y);
  assert(z1);
  assert(z2);

  return 0;
}
