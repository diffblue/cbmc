// Author: Michael Tautschnig

// Test file for exit() call detection
// This file should generate multiple warnings

#include <cstdlib>

int main()
{
  // Basic exit calls - should trigger warnings
  exit(1);            // Line 11: Warning expected
  exit(EXIT_FAILURE); // Line 12: Warning expected

  // Namespace qualified calls - should trigger warnings
  std::exit(1); // Line 15: Warning expected
  ::exit(2);    // Line 16: Warning expected

  // Calls with whitespace - should trigger warnings
  exit(3); // Line 19: Warning expected
  exit(4); // Line 20: Warning expected
  exit(5); // Line 21: Warning expected (tab)

  // Calls in expressions - should trigger warnings
  if(condition)
    exit(6);      // Line 25: Warning expected
  return exit(7); // Line 26: Warning expected

  // Variable names - should NOT trigger warnings
  int exit_code = 0;
  bool exit_flag = false;
  void *exit_ptr = nullptr;

  return exit_code;
}

void error_function()
{
  // More exit calls in different contexts
  exit(10); // Line 39: Warning expected
}

class test_classt
{
public:
  void method()
  {
    exit(11); // Line 47: Warning expected
  }
};

// Function names containing exit - should NOT trigger
void my_exit_function()
{
  return;
}
