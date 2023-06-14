// Positive test for singleton interval simplification.
// Notice that the sequence of the inequalities in this
// expression is different to the one in
// `singleton_interval_in_assume_7690.c`.

int main()
{
  int x;
  __CPROVER_assume(x >= 15 && x <= 15);
  int y = x + 20;

  __CPROVER_assert(
    y != 35, "expected failure: only paths where x == 15 explored");
  __CPROVER_assert(
    y == 34, "expected failure: only paths where x == 15 explored");
  return 0;
}
