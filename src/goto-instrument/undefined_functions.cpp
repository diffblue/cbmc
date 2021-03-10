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

void undefined_function_abort_path(goto_modelt &goto_model)
{
  for(auto &gf_entry : goto_model.goto_functions.function_map)
  {
    for(auto &ins : gf_entry.second.body.instructions)
    {
      if(!ins.is_function_call())
        continue;

      const code_function_callt &call = ins.get_function_call();

      if(call.function().id()!=ID_symbol)
        continue;

      const irep_idt &function=
        to_symbol_expr(call.function()).get_identifier();

      goto_functionst::function_mapt::const_iterator entry=
        goto_model.goto_functions.function_map.find(function);
      DATA_INVARIANT(
        entry!=goto_model.goto_functions.function_map.end(),
        "called function must be in function_map");

      if(entry->second.body_available())
        continue;

      ins = goto_programt::make_assumption(false_exprt(), ins.source_location);
      ins.source_location.set_comment(
        "'" + id2string(function) + "' is undefined");
    }
  }
}
