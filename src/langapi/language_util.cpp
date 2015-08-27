/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <memory>

#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/language.h>
#include <util/std_expr.h>

#include "language_util.h"
#include "mode.h"

/*******************************************************************\

Function: get_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::unique_ptr<languaget> get_language(
  const namespacet &ns,
  const irep_idt &identifier)
{
  if(identifier=="")
    return std::unique_ptr<languaget>(get_default_language());
  else
  {
    const symbolt *symbol;
    
    if(ns.lookup(identifier, symbol))
      return std::unique_ptr<languaget>(get_default_language());
    else if(symbol->mode=="")
      return std::unique_ptr<languaget>(get_default_language());
    else
    {
      languaget *ptr=get_language_from_mode(symbol->mode);

      if(ptr==NULL)
        throw "symbol `"+id2string(symbol->name)+
              "' has unknown mode '"+id2string(symbol->mode)+"'";

      return std::unique_ptr<languaget>(ptr);
    }
  }
}

/*******************************************************************\

Function: from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr)
{
  std::unique_ptr<languaget> p=get_language(ns, identifier);

  std::string result;
  p->from_expr(expr, result, ns);

  return result;
}

/*******************************************************************\

Function: from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_type(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p=get_language(ns, identifier);

  std::string result;
  p->from_type(type, result, ns);

  return result;
}

/*******************************************************************\

Function: from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_expr(const exprt &expr)
{
  symbol_tablet symbol_table;
  return from_expr(namespacet(symbol_table), "", expr);
}

/*******************************************************************\

Function: from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_type(const typet &type)
{
  symbol_tablet symbol_table;
  return from_type(namespacet(symbol_table), "", type);
}

/*******************************************************************\

Function: to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt to_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const std::string &src)
{
  std::unique_ptr<languaget> p=get_language(ns, identifier);
  
  const symbolt &symbol=ns.lookup(identifier);

  exprt expr;

  if(p->to_expr(src, id2string(symbol.module), expr, ns))
    return nil_exprt();
  
  return expr;
}
