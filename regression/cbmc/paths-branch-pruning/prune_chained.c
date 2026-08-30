// Test that branch pruning works with chained assumes and
// nested branches (comparator-style pattern from Collections-C).

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
  int x, y;
  __CPROVER_assume(x < y);

  int r = cmp(x, y);

  // With x < y, cmp must return -1.
  __CPROVER_assert(r == -1, "cmp returns -1 when x < y");

  return 0;
}
