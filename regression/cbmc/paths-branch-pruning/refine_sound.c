// Test that branch pruning is disabled with --refine (used by --incremental-loop).

int main()
{
  int a[10];
  int i;
  __CPROVER_assume(i >= 0 && i < 10);

  a[i] = 42;
  __CPROVER_assert(a[0] == 42, "a[0] is 42");

  return 0;
}
