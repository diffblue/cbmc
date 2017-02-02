/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/prefix.h>
#include <util/config.h>

#include "expr2java.h"
#include "java_bytecode_typecheck.h"

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string java_bytecode_typecheckt::to_string(const exprt &expr)
{
  return expr2java(expr, ns);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string java_bytecode_typecheckt::to_string(const typet &type)
{
  return type2java(type, ns);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_non_type_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_non_type_symbol(symbolt &symbol)
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

void java_bytecode_typecheckt::typecheck()
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

    if(!symbol.is_type)
      continue;

    typecheck_type_symbol(symbol);
  }

  // We now check all non-type symbols
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=symbol_table.symbols[id];

    if(symbol.is_type)
      continue;

    typecheck_non_type_symbol(symbol);
  }
}

/*******************************************************************\

Function: java_bytecode_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  bool string_refinement_enabled)
{
  java_bytecode_typecheckt java_bytecode_typecheck(
    symbol_table, message_handler, string_refinement_enabled);
  return java_bytecode_typecheck.typecheck_main();
}

/*******************************************************************\

Function: java_bytecode_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  #if 0
  symbol_tablet symbol_table;
  java_bytecode_parse_treet java_bytecode_parse_tree;

  java_bytecode_typecheckt java_bytecode_typecheck(
    java_bytecode_parse_tree, symbol_table,
    "", message_handler);

  try
  {
    java_bytecode_typecheck.typecheck_expr(expr);
  }

  catch(int e)
  {
    java_bytecode_typecheck.error();
  }

  catch(const char *e)
  {
    java_bytecode_typecheck.error(e);
  }

  catch(const std::string &e)
  {
    java_bytecode_typecheck.error(e);
  }

  return java_bytecode_typecheck.get_error_found();
  #endif

  // fail for now
  return true;
}

// Static members of java_bytecode_typecheckt:
std::map<irep_idt, irep_idt>
  java_bytecode_typecheckt::string_literal_to_symbol_name;
std::map<irep_idt, size_t>
  java_bytecode_typecheckt::escaped_string_literal_count;
