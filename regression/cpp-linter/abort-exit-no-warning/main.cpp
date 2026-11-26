// Author: Michael Tautschnig

// Test file that should NOT generate any termination warnings
// This file contains various uses of "exit" and "abort" that should not trigger

#include <iostream>
#include <string>

int main()
{
  // Variable names containing exit/abort - should not trigger
  int exit_code = 0;
  bool exit_flag = false;
  void *exit_ptr = nullptr;
  bool abort_flag = false;
  int abort_count = 0;

  // Assignment to variables
  exit_code = 1;
  exit_flag = true;
  abort_flag = false;

  return exit_code;
}

// Function definitions that shouldn't trigger
void my_exit_function()
{
  std::cout << "This is not exit()" << std::endl;
}

void abort_handler()
{
  std::cout << "This is not abort()" << std::endl;
}

// Custom namespace functions (not std:: or ::)
void use_custom_functions()
{
  // These have custom namespace prefixes, so should not trigger
  // Note: current implementation only checks for std:: and :: prefixes
  // myns::exit(0);  // Would not trigger if uncommented
  // custom::abort();  // Would not trigger if uncommented
}

// Member functions named exit()/abort() must NOT trigger: the boundary class
// excludes '.' and '>', so calls via '.' and '->' are ignored. (This file is
// a lint fixture and is not compiled, so a forward declaration suffices; a
// full definition would declare members "void exit();"/"void abort();" whose
// declaration lines the textual check cannot distinguish from calls.)
struct my_handlert;

void member_calls(my_handlert &obj, my_handlert *ptr)
{
  obj.exit();   // member call via '.', should NOT trigger
  obj.abort();  // member call via '.', should NOT trigger
  ptr->exit();  // member call via '->', should NOT trigger
  ptr->abort(); // member call via '->', should NOT trigger
}

// Distinct library functions whose names merely contain exit/abort must NOT
// trigger.
void library_lookalikes()
{
  atexit(nullptr);
  _exit(0);
  pthread_exit(nullptr);
}
