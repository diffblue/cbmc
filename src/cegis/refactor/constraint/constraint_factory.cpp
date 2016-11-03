#include <cegis/refactor/options/refactor_program.h>

void create_constraint_function_caller(refactor_programt &prog)
{
  // * Create function calling all refactored methods
}

void link_refactoring_ranges(refactor_programt &prog)
{
  // * Goto input/spec range
  //   * Repeat possibly skipped local declarations
}

void create_refactoring_constraint(refactor_programt &prog)
{
  // * Nondet state vars at beginning of ranges
  // * Clone state vars
  // * Replace used variables in input range by clones
  // * Generate assertion based on used variables
}
