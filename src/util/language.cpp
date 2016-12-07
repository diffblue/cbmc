/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract interface to support a programming language

#include "language.h"
#include "expr.h"
#include <util/config.h>
#include <goto-programs/goto_functions.h>

bool languaget::final(symbol_tablet &symbol_table)
{
  return false;
}

bool languaget::interfaces(symbol_tablet &symbol_table)
{
  return false;
}

void languaget::dependencies(
  const std::string &module,
  std::set<std::string> &modules)
{
}

bool languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr.pretty();
  return false;
}

bool languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type.pretty();
  return false;
}

bool languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns)
{
  // probably ansi-c/type2name could be used as better fallback if moved to
  // util/
  name=type.pretty();
  return false;
}

}

/// Generate a entry function for a specific function. Should be overriden in
/// derived languagets
/// \param entry_function_symbol: The symbol for the function that should be
///   used as the entry point
/// \param symbol_table: The symbol table for the program. The new _start
///   function symbol will be added to this table
/// \return Returns false if the entry method was generated correctly
bool languaget::generate_start_function(
  const symbolt &entry_function_symbol,
  symbol_tablet &symbol_table)
{
  // Implement in derived languagets
  assert(0);
  return true;
}

/// To replace an existing _start function with a new one that calls a specified
/// function
/// \param required_entry_function: a code symbol inside the symbol table which
///   is the function that should be used as the entry point.
/// \param symbol_table: the symbol table for the program. The _start symbol
///   will be replaced with a new start function
/// \param goto_functions: the functions for the goto program. The _start
///   function will be erased from this
/// \return Returns false if the new start function is created successfully,
///   true otherwise.
bool languaget::regenerate_start_function(
  const symbolt &entry_function_symbol,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  // Remove the existing _start function so we can create a new one
  symbol_table.remove(goto_functionst::entry_point());

  bool return_code=generate_start_function(entry_function_symbol, symbol_table);

  // Remove the function from the goto_functions so is copied back in
  // from the symbol table
  if(!return_code)
  {
    const auto &start_function=
      goto_functions.function_map.find(goto_functionst::entry_point());
    if(start_function!=goto_functions.function_map.end())
    {
      goto_functions.function_map.erase(start_function);
    }
  }

  return return_code;