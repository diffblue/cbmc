// Test that branch pruning does NOT prune feasible branches.
// Both branches of a nondet condition must be explored.

int main()
{
  int x;

  if(x > 0)
    __CPROVER_assert(0, "positive branch reachable");
  else
    __CPROVER_assert(0, "non-positive branch reachable");

  return 0;
}
