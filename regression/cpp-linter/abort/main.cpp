// Author: Michael Tautschnig

// Test file for abort() call detection
// This file should generate multiple warnings

#include <cstdlib>

void error_handler()
{
  // Basic abort calls - should trigger warnings
  abort(); // Line 11: Warning expected

  // Namespace qualified calls - should trigger warnings
  std::abort(); // Line 14: Warning expected
  ::abort();    // Line 15: Warning expected

  // Calls with whitespace - should trigger warnings
  abort(); // Line 18: Warning expected
  abort(); // Line 19: Warning expected
  abort(); // Line 20: Warning expected (tab)

  // Calls in expressions - should trigger warnings
  if(fatal_error)
    abort(); // Line 24: Warning expected
}

// Variable names - should NOT trigger warnings
bool abort_flag = false;
int abort_count = 0;

class abortablet
{
public:
  void process()
  {
    if(should_abort)
    {
      abort(); // Line 38: Warning expected
    }
  }
};

// Function names containing abort - should NOT trigger
void abort_operation()
{
  return;
}

void check_abort_status()
{
  return;
}
