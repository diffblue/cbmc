/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include "goto_state.h"

#include <util/format_expr.h>

/// Print the constant propagation map in a human-friendly format.
/// This is primarily for use from the debugger; please don't delete me just
/// because there aren't any current callers.
void goto_statet::output_propagation_map(std::ostream &out)
{
  for(const auto &name_value : propagation)
  {
    out << name_value.first << " <- " << format(name_value.second) << "\n";
  }
}
