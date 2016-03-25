/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#include <util/symbol_table.h>

#include "expr2jsil.h"

#include "jsil_typecheck.h"

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string jsil_typecheckt::to_string(const exprt &expr)
{
  return expr2jsil(expr, ns);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string jsil_typecheckt::to_string(const typet &type)
{
  return type2jsil(type, ns);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_non_type_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_non_type_symbol(symbolt &symbol)
{
  assert(!symbol.is_type);
  typecheck_type(symbol.type);
  typecheck_expr(symbol.value);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck()
{
  // The hash table iterators are not stable,
  // and we might add new symbols.

  std::vector<irep_idt> identifiers;
  identifiers.reserve(symbol_table.symbols.size());
  forall_symbols(s_it, symbol_table.symbols)
    identifiers.push_back(s_it->first);

  // We first check all type symbols,
  // recursively doing base classes first.
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=symbol_table.symbols[id];

    if(symbol.is_type)
      typecheck_type_symbol(symbol);
  }

  // We now check all non-type symbols
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=symbol_table.symbols[id];

    if(!symbol.is_type)
      typecheck_non_type_symbol(symbol);
  }
}

/*******************************************************************\

Function: jsil_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  jsil_typecheckt jsil_typecheck(symbol_table, message_handler);
  return jsil_typecheck.typecheck_main();
}

/*******************************************************************\

Function: jsil_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  symbol_tablet symbol_table;

  jsil_typecheckt jsil_typecheck(
    symbol_table,
    message_handler);

  try
  {
    jsil_typecheck.typecheck_expr(expr);
  }

  catch(int e)
  {
    jsil_typecheck.error_msg();
  }

  catch(const char *e)
  {
    jsil_typecheck.str << e;
    jsil_typecheck.error_msg();
  }

  catch(const std::string &e)
  {
    jsil_typecheck.str << e;
    jsil_typecheck.error_msg();
  }

  return jsil_typecheck.get_error_found();
}
