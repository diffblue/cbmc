int main()
{
  int a[10];
  int c[10];

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  // C# style
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<9+1) ==> a[i]>=1 && a[i]<=10 });
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<10) ==>  __CPROVER_forall{int j; (j>i && j<10) ==> a[j]>a[i]} });
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<9) ==> c[i+1]>=c[i] });


  __CPROVER_assert(__CPROVER_forall {unsigned i; (i>=0 && i<10) ==> a[i]>=1 && a[i]<=10}, "forall a[]");
  assert(a[9]>a[1]);
  assert(a[2]>a[3]);
  __CPROVER_assert(__CPROVER_forall {unsigned i; (i>=1 && i<10) ==> c[i-1]<=c[i]}, "forall c[]");
  assert(c[3]>=c[1]);
  // clang-format on
  return 0;
}
