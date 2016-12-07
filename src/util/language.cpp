/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "language.h"
#include "expr.h"
#include <util/config.h>
#include <util/symbol.h>
#include <util/symbol_table.h>
#include <goto-programs/goto_functions.h>

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

/*******************************************************************\

Function: languaget::regenerate_start_function

  Inputs:
          required_entry_function - a code symbol inside the symbol
                                    table which is the function that
                                    should be used as the entry point.

          symbol_table - the symbol table for the program. The _start
                         symbol will be replaced with a new start function

          goto_functions - the functions for the goto program. The _start
                           function will be erased from this

 Outputs: Returns false if the new start function is created successfully,
          true otherwise.

 Purpose: To replace an existing _start function with a new one that
          calls a specified function

\*******************************************************************/
bool languaget::regenerate_start_function(
  const symbolt &entry_function_symbol,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  // Remove the existing _start function so we can create a new one
  symbol_table.remove(ID__start);

  bool return_code=generate_start_function(entry_function_symbol, symbol_table);

  // Remove the function from the goto_functions so is copied back in
  // from the symbol table
  if(!return_code)
  {
    const auto &start_function=goto_functions.function_map.find(ID__start);
    if(start_function!=goto_functions.function_map.end())
    {
      goto_functions.function_map.erase(start_function);
    }
  }

  return return_code;
}
