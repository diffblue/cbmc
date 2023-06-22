// Negative test for singleton interval simplification.

int main()
{
  int x;
  int y = x + 20;

  __CPROVER_assert(
    y != -6, "expected failure: paths where x is unbounded explored");

  __CPROVER_assume(x >= 0 && x <= 15);
  __CPROVER_assert(
    y != 34, "expected failure: paths where 0 <= x <= 15 explored");

  int z = x + 20;
  __CPROVER_assert(z != 36, "expected success: paths where x <= 15 explored");
  return 0;
}
