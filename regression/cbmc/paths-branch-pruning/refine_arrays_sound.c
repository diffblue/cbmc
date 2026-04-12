// Test that branch pruning is disabled with --refine-arrays
// and does not cause unsound results.

extern int __VERIFIER_nondet_int();

int main()
{
  int a[10];
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(i >= 0 && i < 10);

  a[i] = 42;

  // This should be found as a failure: a[0] may or may not be 42
  // depending on i. With --refine-arrays, the solver needs the
  // refinement loop to determine this.
  __CPROVER_assert(a[0] == 42, "a[0] is 42");

  return 0;
}
