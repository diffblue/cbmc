int main()
{
  int b[2];
  int c[2];

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  __CPROVER_assume( __CPROVER_forall { char i; (i>=0 && i<2) ==> b[i]>=10 && b[i]<=10 } );
  __CPROVER_assume( __CPROVER_forall { unsigned i; (i>=0 && i<2) ==> c[i]>=10 && c[i]<=10 } );
  // clang-format on

  assert(b[0] == 10 && b[1] == 10);
  assert(c[0] == 10 && c[1] == 10);

  return 0;
}
