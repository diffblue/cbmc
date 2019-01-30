int main()
{

  int a[3][3];
  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  // NOLINTNEXTLINE(whitespace/line_length)
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<5) ==>  __CPROVER_exists{int j; (j>=i && j<3) && a[i][j]==10} });
  // clang-format on

  assert(a[0][0]==10||a[0][1]==10||a[0][2]==10);

  return 0;
}
