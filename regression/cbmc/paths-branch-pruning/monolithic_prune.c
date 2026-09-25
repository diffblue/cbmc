// Test that branch pruning works in monolithic (non-paths) mode.
// The comparator branches are determined by the __CPROVER_assume,
// so the solver can prune infeasible directions.

int cmp(int a, int b)
{
  if(a < b)
    return -1;
  if(a == b)
    return 0;
  return 1;
}

int main()
{
  int x, y, z;
  __CPROVER_assume(x < y && y < z);

  __CPROVER_assert(cmp(x, y) == -1, "x < y");
  __CPROVER_assert(cmp(y, z) == -1, "y < z");
  __CPROVER_assert(cmp(x, z) == -1, "x < z");

  return 0;
}
