/*******************************************************************\

Module: Misc Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Misc Utilities

#include "array_name.h"

#include "expr.h"
#include "invariant.h"
#include "namespace.h"
#include "ssa_expr.h"
#include "symbol.h"

std::string array_name(
  const namespacet &ns,
  const exprt &expr)
{
  if(expr.id()==ID_index)
  {
    return array_name(ns, to_index_expr(expr).array()) + "[]";
  }
  else if(is_ssa_expr(expr))
  {
    const symbolt &symbol=
      ns.lookup(to_ssa_expr(expr).get_object_name());
    return "array `"+id2string(symbol.base_name)+"'";
  }
  else if(expr.id()==ID_symbol)
  {
    const symbolt &symbol = ns.lookup(to_symbol_expr(expr));
    return "array `"+id2string(symbol.base_name)+"'";
  }
  else if(expr.id()==ID_string_constant)
  {
    return "string constant";
  }
  else if(expr.id()==ID_member)
  {
    const member_exprt &member_expr = to_member_expr(expr);

    return array_name(ns, member_expr.compound()) + "." +
           id2string(member_expr.get_component_name());
  }

  return "array";
}
