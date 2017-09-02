/*******************************************************************\

Module: Remove function definition

Author: Michael Tautschnig

Date: April 2017

\*******************************************************************/

/// \file
/// Remove function definition

#include "remove_function.h"

#include <util/message.h>

#include <goto-programs/goto_functions.h>

/// Remove the body of function "identifier" such that an analysis will treat it
/// as a side-effect free function with non-deterministic return value.
/// \par parameters: symbol_table  Input symbol table to be modified
/// goto_functions  Input functions to be modified
/// identifier  Function to be removed
/// message_handler  Error/status output
void remove_function(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const irep_idt &identifier,
  message_handlert &message_handler)
{
  messaget message(message_handler);

  goto_functionst::function_mapt::iterator entry=
    goto_functions.function_map.find(identifier);

  if(entry==goto_functions.function_map.end())
  {
    message.error() << "No function " << identifier
                    << " in goto program" << messaget::eom;
    return;
  }
  else if(entry->second.is_inlined())
  {
    message.warning() << "Function " << identifier << " is inlined, "
                      << "instantiations will not be removed"
                      << messaget::eom;
  }

  if(entry->second.body_available())
  {
    message.status() << "Removing body of " << identifier
                     << messaget::eom;
    entry->second.clear();
    symbol_table.at(identifier).value.make_nil();
  }
}

/// Remove the body of all functions listed in "names" such that an analysis
/// will treat it as a side-effect free function with non-deterministic return
/// value.
/// \par parameters: symbol_table  Input symbol table to be modified
/// goto_functions  Input functions to be modified
/// names  List of functions to be removed
/// message_handler  Error/status output
void remove_functions(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  const std::list<std::string> &names,
  message_handlert &message_handler)
{
  for(const auto &f : names)
    remove_function(symbol_table, goto_functions, f, message_handler);
}
