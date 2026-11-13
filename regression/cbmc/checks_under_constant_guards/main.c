int main()
{
  int a[4];
  unsigned i;
  __CPROVER_assume(i < 4);
  // after a constant operand that does not decide the result, the checks
  // of `a[i]' are the unguarded ones: each is made once
  int r = 0 || a[i] == 1;
  int s = 1 && a[i] == 2;
  int t = 1 ? a[i] : 0;
  // the operand is not evaluated: no check
  int u = 1 || a[i + 4] == 1;
  int v = 0 ? a[i + 4] : 0;
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
