/*******************************************************************\

Module: Program Transformation

Author: diffblue

\*******************************************************************/

/// \file
/// Program Transformation

#include "collect_function_pointer_targets.h"
collect_function_pointer_targetst::collect_function_pointer_targetst(
  message_handlert &message_handler,
  const symbol_tablet &symbol_table,
  bool only_resolve_const_fps)
  : log(message_handler),
    ns(symbol_table),
    symbol_table(symbol_table),
    only_resolve_const_fps(only_resolve_const_fps),
    initialised(false)
{
}

void collect_function_pointer_targetst::initialise_taken_addresses(
  const goto_functionst &goto_functions)
{
  for(const auto &s : symbol_table.symbols)
    compute_address_taken_functions(s.second.value, address_taken);

  compute_address_taken_functions(goto_functions, address_taken);
}

void collect_function_pointer_targetst::initialise_type_map(
  const goto_functionst &goto_functions)
{
  for(const auto &fmap_pair : goto_functions.function_map)
    type_map.emplace(fmap_pair.first, fmap_pair.second.type);
}

