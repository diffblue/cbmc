// Test case for nested loops in k-induction instrumentation.
// This used to cause segmentation faults because the code incorrectly assumed
// loop heads always have conditions and didn't handle nested loop iterator
// invalidation.
int main()
{
  unsigned i = 0;
  unsigned j;
  while(i < 2)
  {
    j = 0;
    while(j < 2)
    {
      j++;
    }
    __CPROVER_assert(j == 2, "inner loop terminates at 2");
    i++;
  }
}
