/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>
#include <prefix.h>
#include <config.h>

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

Function: java_bytecode_typecheckt::typecheck_function_body

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_typecheckt::typecheck_function_body(symbolt &symbol)
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
  for(java_bytecode_parse_treet::itemst::iterator
      it=parse_tree.items.begin();
      it!=parse_tree.items.end();
      it++)
  {
  }
}

/*******************************************************************\

Function: java_bytecode_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_typecheck(
  java_bytecode_parse_treet &java_bytecode_parse_tree,
  contextt &context,
  const std::string &module,
  message_handlert &message_handler)
{
  java_bytecode_typecheckt java_bytecode_typecheck(
    java_bytecode_parse_tree, context, module, message_handler);
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
  contextt context;
  java_bytecode_parse_treet java_bytecode_parse_tree;

  java_bytecode_typecheckt java_bytecode_typecheck(
    java_bytecode_parse_tree, context,
    ns.get_context(), "", message_handler);

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
}
