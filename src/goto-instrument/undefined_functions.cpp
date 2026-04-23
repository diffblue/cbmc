/*******************************************************************\

Module: Handling of functions without body

Author: Michael Tautschnig

Date: July 2016

\*******************************************************************/

/// \file
/// Handling of functions without body

#include "undefined_functions.h"

#include <ostream>

#include <util/invariant.h>

#include <goto-programs/goto_model.h>

void list_undefined_functions(
  const goto_modelt &goto_model,
  std::ostream &os)
{
  const namespacet ns(goto_model.symbol_table);

  for(const auto &gf_entry : goto_model.goto_functions.function_map)
  {
    if(!ns.lookup(gf_entry.first).is_macro && !gf_entry.second.body_available())
      os << gf_entry.first << '\n';
  }
}
