// If-conversion snapshots the branch condition before linearising a region.
// This is required for soundness when an earlier assignment in the region
// overwrites a variable that the condition reads: the generated conditional
// expressions must all use the condition's value as it was at the branch, not
// a value clobbered part-way through the region.
//
// Here the branch is taken (x = 1 > 0), so the original program sets y = 7.
// Without snapshotting, the rewrite of `y = 7` would re-evaluate `x > 0` after
// `x` had been set to -5, wrongly leaving y at 9 and reporting a spurious
// counterexample under --paths.

int main(void)
{
  int x = 1;
  int y = 9;

  if(x > 0)
  {
    x = -5;
    y = 7;
  }

  __CPROVER_assert(y == 7, "the branch is taken, so y is 7");

  return 0;
}
