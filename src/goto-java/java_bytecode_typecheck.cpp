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
  return expr2c(expr, *this);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string java_bytecode_typecheckt::to_string(const typet &type)
{ 
  return type2c(type, *this);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_expr(exprt &expr)
{ 
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck()
{
}

/*******************************************************************\

Function: java_bytecode_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_typecheck(
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  java_bytecode_typecheckt java_bytecode_typecheck(
    symbol_table, module, message_handler);
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
