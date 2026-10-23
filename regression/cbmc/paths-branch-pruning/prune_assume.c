// Test that branch pruning correctly prunes infeasible branches
// determined by __CPROVER_assume constraints.

int main()
{
  int x;
  __CPROVER_assume(x > 0);

  // Branch pruning should determine that x <= 0 is infeasible,
  // so only the true branch is explored.
  if(x > 0)
  {
    // reachable
    __CPROVER_assert(1, "reachable path");
  }
  else
  {
    // unreachable — pruned by solver
    __CPROVER_assert(0, "unreachable path");
  }

  return 0;
}
