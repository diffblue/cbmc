/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_typecheck.h"

/*******************************************************************\

Function: ansi_c_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_typecheckt::typecheck()
{
  for(ansi_c_parse_treet::itemst::iterator
      it=parse_tree.items.begin();
      it!=parse_tree.items.end();
      it++)
  {
    if(it->id()==ID_declaration)
    {
      ansi_c_declarationt &declaration=
        to_ansi_c_declaration(*it);

      symbolt symbol;
      declaration.to_symbol(symbol);
      typecheck_symbol(symbol);
    }
    else if(it->id()==ID_initializer)
    {
    }
    else
      assert(false);
  }
}

/*******************************************************************\

Function: ansi_c_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_typecheck(
  ansi_c_parse_treet &ansi_c_parse_tree,
  contextt &context,
  const std::string &module,
  message_handlert &message_handler)
{
  ansi_c_typecheckt ansi_c_typecheck(
    ansi_c_parse_tree, context, module, message_handler);
  return ansi_c_typecheck.typecheck_main();
}

/*******************************************************************\

Function: ansi_c_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  contextt context;
  ansi_c_parse_treet ansi_c_parse_tree;

  ansi_c_typecheckt ansi_c_typecheck(
    ansi_c_parse_tree, context,
    ns.get_context(), "", message_handler);

  try
  {
    ansi_c_typecheck.typecheck_expr(expr);
  }

  catch(int e)
  {
    ansi_c_typecheck.error();
  }

  catch(const char *e)
  {
    ansi_c_typecheck.error(e);
  }

  catch(const std::string &e)
  {
    ansi_c_typecheck.error(e);
  }
  
  return ansi_c_typecheck.get_error_found();
}
