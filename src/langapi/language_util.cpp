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

static languaget* get_language(
  const namespacet &ns,
  const irep_idt &identifier)
{
  const symbolt *symbol;

  if(identifier=="" ||
     ns.lookup(identifier, symbol) ||
     symbol->mode=="")
    return get_default_language();

  languaget *ptr=get_language_from_mode(symbol->mode);

  if(ptr==NULL)
    throw "symbol `"+id2string(symbol->name)+
      "' has unknown mode '"+id2string(symbol->mode)+"'";

  return ptr;
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
  std::unique_ptr<languaget> p(get_language(ns, identifier));

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
  std::unique_ptr<languaget> p(get_language(ns, identifier));

  std::string result;
  p->from_type(type, result, ns);

  return result;
}

/*******************************************************************\

Function: type_to_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type_to_name(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(get_language(ns, identifier));

  std::string result;
  p->type_to_name(type, result, ns);

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
  std::unique_ptr<languaget> p(get_language(ns, identifier));

  const symbolt &symbol=ns.lookup(identifier);

  exprt expr;

  if(p->to_expr(src, id2string(symbol.module), expr, ns))
    return nil_exprt();

  return expr;
}

/*******************************************************************\

Function: type_to_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type_to_name(const typet &type)
{
  symbol_tablet symbol_table;
  return type_to_name(namespacet(symbol_table), "", type);
}
