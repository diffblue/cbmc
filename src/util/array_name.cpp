/*******************************************************************\

Module: Misc Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Misc Utilities

#include "array_name.h"

#include "expr.h"
#include "namespace.h"
#include "symbol.h"
#include "ssa_expr.h"

std::string array_name(
  const namespacet &ns,
  const exprt &expr)
{
  if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index takes two operands";

    return array_name(ns, expr.op0())+"[]";
  }
  else if(is_ssa_expr(expr))
  {
    const symbolt &symbol=
      ns.lookup(to_ssa_expr(expr).get_object_name());
    return "array `"+id2string(symbol.base_name)+"'";
  }
  else if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=ns.lookup(expr);
    return "array `"+id2string(symbol.base_name)+"'";
  }
  else if(expr.id()==ID_string_constant)
  {
    return "string constant";
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    return array_name(ns, expr.op0())+"."+
           expr.get_string(ID_component_name);
  }

  return "array";
}
