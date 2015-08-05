/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_types.h>
#include <util/prefix.h>
#include <util/config.h>

#include <ansi-c/expr2c.h>

#include "java_bytecode_typecheck.h"

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string java_bytecode_typecheckt::to_string(const exprt &expr)
{ 
  return expr2c(expr, ns);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string java_bytecode_typecheckt::to_string(const typet &type)
{ 
  return type2c(type, ns);
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
  // This is complicated by the fact that hash_map iterators
  // get invalidated when inserting!
  // The references stay valid, luckily.
  
  std::vector<irep_idt> symbols;
  symbols.reserve(symbol_table.symbols.size());
  
  for(symbol_tablet::symbolst::iterator
      s_it=symbol_table.symbols.begin();
      s_it!=symbol_table.symbols.end();
      s_it++)
    symbols.push_back(s_it->first);
  
  // We first check all type symbols,
  // recursively doing base classes first.
  for(std::vector<irep_idt>::const_iterator
      s_it=symbols.begin();
      s_it!=symbols.end();
      s_it++)
  {
    symbolt &symbol=symbol_table.symbols[*s_it];
    
    if(!symbol.is_type)
      continue;
  
    // already done?
    if(!already_typechecked.insert(*s_it).second)
      continue;
  
    typecheck_type_symbol(symbol);
  }

  // We now check all non-type symbols
  for(std::vector<irep_idt>::const_iterator
      s_it=symbols.begin();
      s_it!=symbols.end();
      s_it++)
  {
    symbolt &symbol=symbol_table.symbols[*s_it];
    
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
  message_handlert &message_handler)
{
  java_bytecode_typecheckt java_bytecode_typecheck(
    symbol_table, message_handler);
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
