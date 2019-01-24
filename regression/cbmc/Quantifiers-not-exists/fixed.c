int main()
{
  int a[2][2];
  int b[2][2];
  int c[2][2];
  int d[2][2];

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  // NOLINTNEXTLINE(whitespace/line_length)
  __CPROVER_assume(!__CPROVER_exists { int i; (i>=0 && i<2) && (__CPROVER_exists{int j; (j>=0 && j<2) && a[i][j]<=10}) });

  assert(0);

  // NOLINTNEXTLINE(whitespace/line_length)
  __CPROVER_assume(__CPROVER_forall { int i; (i>=0 && i<2) ==> (!__CPROVER_exists{int j; (j>=0 && j<2) && b[i][j]>=1 && b[i][j]<=10}) });

  assert(0);

  // NOLINTNEXTLINE(whitespace/line_length)
  __CPROVER_assume(!__CPROVER_exists { int i; (i>=0 && i<2) && (!__CPROVER_exists{int j; (j>=0 && j<2) && (c[i][j]==0 || c[i][j]<=10)}) });

  assert(0);

  // NOLINTNEXTLINE(whitespace/line_length)
  __CPROVER_assume(!__CPROVER_exists { int i; (i>=0 && i<2) && (__CPROVER_forall{int j; (j>=0 && j<2) ==> d[i][j]>=1 && d[i][j]<=10}) });
  // clang-format on

  assert(0);

  assert(a[0][0] > 10);

  assert((b[0][0] < 1 || b[0][0] > 10) && (b[0][1] < 1 || b[0][1] > 10));
  assert((b[1][0] < 1 || b[1][0] > 10) && (b[1][1] < 1 || b[1][1] > 10));

  assert(c[0][0] == 0 || c[0][1] == 0 || c[1][0] <= 10 || c[1][1] <= 10);

  assert(((d[0][0] < 1 || d[0][0] > 10) || (d[0][1] < 1 || d[0][1] > 10)));
  assert(((d[1][0] < 1 || d[1][0] > 10) || (d[1][1] < 1 || d[1][1] > 10)));

  return 0;
}
