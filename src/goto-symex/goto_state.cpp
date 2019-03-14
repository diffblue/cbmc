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

std::size_t goto_statet::increase_generation(
  const irep_idt l1_identifier,
  const ssa_exprt &lhs,
  std::function<std::size_t(const irep_idt &)> fresh_l2_name_provider)
{
  auto current_emplace_res =
    level2.current_names.emplace(l1_identifier, std::make_pair(lhs, 0));

  current_emplace_res.first->second.second =
    fresh_l2_name_provider(l1_identifier);

  return current_emplace_res.first->second.second;
}
