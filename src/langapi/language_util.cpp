/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <memory>

#include "language_util.h"
#include "mode.h"

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
  std::auto_ptr<languaget> p;

  if(identifier=="")
    p=std::auto_ptr<languaget>(get_default_language());
  else
  {
    const symbolt *symbol;
    
    if(ns.lookup(identifier, symbol))
      p=std::auto_ptr<languaget>(get_default_language());
    else if(symbol->mode=="")
      p=std::auto_ptr<languaget>(get_default_language());
    else
    {
      languaget *ptr=get_language_from_mode(symbol->mode);

      if(ptr==NULL)
        throw "symbol `"+id2string(symbol->name)+
              "' has unknown mode '"+id2string(symbol->mode)+"'";

      p=std::auto_ptr<languaget>(ptr);
    }
  }

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
  std::auto_ptr<languaget> p;

  if(identifier=="")
    p=std::auto_ptr<languaget>(get_default_language());
  else
  {
    const symbolt *symbol;
    
    if(ns.lookup(identifier, symbol))
      p=std::auto_ptr<languaget>(get_default_language());
    else if(symbol->mode=="")
      p=std::auto_ptr<languaget>(get_default_language());
    else
    {
      languaget *ptr=get_language_from_mode(symbol->mode);

      if(ptr==NULL)
        throw "symbol `"+id2string(symbol->name)+
              "' has unknown mode '"+id2string(symbol->mode)+"'";

      p=std::auto_ptr<languaget>(ptr);
    }
  }

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
  contextt context;
  return from_expr(namespacet(context), "", expr);
}

/*******************************************************************\

Function: from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_type(const typet &type)
{
  contextt context;
  return from_type(namespacet(context), "", type);
}

