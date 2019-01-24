int main()
{
  int a[2];
  int b[2];

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  __CPROVER_assume( __CPROVER_forall { float i; (i>=0 && i<2) ==> a[i]>=10 && a[i]<=10 } );
  __CPROVER_assume( __CPROVER_forall { char i; (i>=0 && i<2) ==> b[i]>=10 && b[i]<=10 } );
  // clang-format on

  assert(a[0]==10 && a[1]==10);
  assert(b[0]==10 && b[1]==10);

  return 0;
}
