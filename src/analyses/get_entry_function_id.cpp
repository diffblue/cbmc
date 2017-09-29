/*******************************************************************\

 Module: Find User Entry Point

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#include "get_entry_function_id.h"

#include <algorithm>

/// Find the name of the user entry function in the current __CPROVER_start
/// entry point.
/// \param symbol_table: The symbol table for the program
/// \param goto_functions: The goto functions for the progam
/// \return The identifier of the function
const irep_idt get_entry_function_id(const goto_functionst &goto_functions)
{
  const auto &entry_function=
    goto_functions.function_map.find(goto_functionst::entry_point());

  INVARIANT(
    entry_function!=goto_functions.function_map.cend(),
    "Entry point must already exist in the binary");

  const auto &last_function_call=std::find_if(
    entry_function->second.body.instructions.rbegin(),
    entry_function->second.body.instructions.rend(),
    [](const goto_programt::instructiont &instruction){
      return instruction.is_function_call();
    });

  INVARIANT(
    last_function_call->code.id()==ID_code,
    "Function call instructions must have a function call codet associated with them"); // NOLINT(*)
  const codet &statement=last_function_call->code.first_statement();
  const code_function_callt &entry_call=
    to_code_function_call(statement);

  INVARIANT(
    entry_call.function().id()==ID_symbol,
    "Function calls are done via symbols");

  return id2string(to_symbol_expr(entry_call.function()).get_identifier());
}
