// Test that guarded assumes are handled correctly by branch pruning.
// The assume inside the if-branch has a non-trivial guard.

int main()
{
  int x, y;
  __CPROVER_assume(x > 0);

  if(y > 0)
  {
    __CPROVER_assume(x < 10);
  }

  // On the path where y > 0: x in (0, 10), so x > 5 is feasible
  // On the path where y <= 0: x > 0, so x > 5 is feasible
  // Both paths should reach this assertion
  if(x > 5)
    __CPROVER_assert(0, "x > 5 reachable");

  // On the path where y > 0: x < 10, so x >= 10 is infeasible
  // On the path where y <= 0: x > 0, so x >= 10 is feasible
  if(x >= 10)
    __CPROVER_assert(0, "x >= 10 reachable");

  return 0;
}
