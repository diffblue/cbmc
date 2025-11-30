// Test for issue #826: Basic blocks incorrectly considered covered
// with unsatisfiable ASSUME statements
//
// This test demonstrates that basic blocks should only be marked as
// covered when ALL instructions in the block can execute, including
// ASSUME statements.
//
// Before the fix: Block 3 would be incorrectly marked as SATISFIED
//   because the coverage assertion was at the beginning of the block.
// After the fix: Block 3 is correctly marked as FAILED because the
//   ASSUME statement is unsatisfiable (x >= 0 when x < 0).

int main()
{
  int x;

  // Block with satisfiable ASSUME - should be covered
  if(x > 0)
  {
    __CPROVER_assume(x > 0);
    return 1;
  }

  // Block with unsatisfiable ASSUME - should NOT be covered
  if(x < 0)
  {
    __CPROVER_assume(x >= 0);
    return 2;
  }

  // Block with no ASSUME - should be covered
  return 0;
}
