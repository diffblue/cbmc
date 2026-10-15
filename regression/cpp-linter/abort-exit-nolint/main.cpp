// Author: Michael Tautschnig

// Test file for NOLINT suppression
// This file tests that NOLINT comments properly suppress warnings

#include <cstdlib>

int main()
{
  // These should be suppressed by NOLINT comments
  exit(1); // NOLINT - justified use case
  abort(); // NOLINT(runtime/termination) - specific suppression

  std::exit(2); // NOLINT
  ::abort();    // NOLINT(runtime/termination)

  // These should still trigger warnings (no NOLINT)
  exit(3); // Line 18: Warning expected
  abort(); // Line 19: Warning expected

  // Test NOLINT with other categories (should NOT suppress this warning)
  exit(4); // NOLINT(whitespace/parens)

  return 0;
}

void test_function()
{
  // Mixed suppressed and unsuppressed
  exit(5);      // Line 30: Warning expected
  abort();      // NOLINT - suppressed
  std::exit(6); // Line 32: Warning expected
  ::abort();    // NOLINT(runtime/termination) - suppressed
}

// Test NOLINT at end of line vs middle
void another_test()
{
  exit(7); /* NOLINT */
  int x = 0;
  abort(); // Line 41: Warning expected
  int y = 0;
}
