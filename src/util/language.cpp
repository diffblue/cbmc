/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "language.h"
#include "expr.h"

/*******************************************************************\

Function: languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::final(symbol_tablet &symbol_table)
{
  return false;
}

/*******************************************************************\

Function: languaget::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::interfaces(symbol_tablet &symbol_table)
{
  return false;
}

/*******************************************************************\

Function: languaget::dependencies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void languaget::dependencies(
  const std::string &module,
  std::set<std::string> &modules)
{
}

/*******************************************************************\

Function: languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr.pretty();
  return false;
}

/*******************************************************************\

Function: languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type.pretty();
  return false;
}

/*******************************************************************\

Function: languaget::type_to_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: generate_start_function

  Inputs:
          entry_function_symbol - The symbol for the function that should
                                  be used as the entry point
          symbol_table - The symbol table for the program. The new _start
                         function symbol will be added to this table

 Outputs: Returns false if the _start method was generated correctly

 Purpose: Generate a _start function for a specific function. Should
          be overriden in derived languagets

\*******************************************************************/
bool languaget::generate_start_function(
  const symbolt &entry_function_symbol,
  symbol_tablet &symbol_table)
{
  // Implement in derived languagets
  assert(0);
  return true;
}
