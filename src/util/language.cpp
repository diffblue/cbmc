/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "language.h"
#include "expr.h"
#include <util/symbol.h>
#include <util/symbol_table.h>

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

Function: languaget::generate_opaque_method_stubs

  Inputs:
          symbol_table - the symbol table for the program

 Outputs:

 Purpose: When there are opaque methods (e.g. ones where we don't
          have a body), we create a stub function in the goto
          program and mark it as opaque so the interpreter fills in
          appropriate values for it.

\*******************************************************************/

void languaget::generate_opaque_method_stubs(symbol_tablet &symbol_table)
{
  for(auto &symbol_entry : symbol_table.symbols)
  {
    if(is_symbol_opaque_function(symbol_entry.second))
    {
      symbolt &symbol=symbol_entry.second;

      irep_idt return_symbol_id = generate_opaque_stub_body(
        symbol,
        symbol_table);

      if(return_symbol_id!=ID_nil)
      {
        symbol.type.set("opaque_method_capture_symbol", return_symbol_id);
      }
    }
  }
}

/*******************************************************************\

Function: languaget::generate_opaque_stub_body

  Inputs:
          symbol - the function symbol which is opaque
          symbol_table - the symbol table

 Outputs: The identifier of the return variable. ID_nil if the function
          doesn't return anything.

 Purpose: To generate the stub function for the opaque function in
          question. The identifier is used in the flag to the interpreter
          that the function is opaque. This function should be implemented
          in the languages.

\*******************************************************************/

irep_idt languaget::generate_opaque_stub_body(
  symbolt &symbol,
  symbol_tablet &symbol_table)
{
  return ID_nil;
}


/*******************************************************************\

Function: languaget::is_symbol_opaque_function

  Inputs:
          symbol - the symbol to be checked

 Outputs: True if the symbol is an opaque (e.g. non-bodied) function

 Purpose: To identify if a given symbol is an opaque function and
          hence needs to be stubbed

\*******************************************************************/

bool languaget::is_symbol_opaque_function(const symbolt &symbol)
{
  return !symbol.is_type &&
    symbol.value.id()==ID_nil &&
    symbol.type.id()==ID_code;
}
