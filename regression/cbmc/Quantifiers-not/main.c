int main()
{
  int a[2];
  a[0]=1;
  a[1]=2;

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  if(!__CPROVER_forall { int i; (i>=0 && i<2) ==> a[i]>=1 && a[i]<=10 })
    __CPROVER_assert(0, "success 1");

  if(!__CPROVER_exists { int i; (i>=0 && i<2) && a[i]>=1 && a[i]<=10 })
    __CPROVER_assert(0, "success 2");

  if(!__CPROVER_forall { int i; (i>=0 && i<2) ==> a[i]>=2 && a[i]<=10 })
    __CPROVER_assert(0, "failure 1");

  if(!__CPROVER_exists { int i; (i>=0 && i<2) && a[i]>=2 && a[i]<=10 })
    __CPROVER_assert(0, "success 3");

  if(!__CPROVER_exists { int i; (i>=0 && i<2) && a[i]>=5 && a[i]<=10 })
    __CPROVER_assert(0, "failure 2");
  // clang-format on

  return 0;
}
