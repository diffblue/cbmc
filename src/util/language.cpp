/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Abstract interface to support a programming language

#include "language.h"
#include "expr.h"

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
