/*******************************************************************\

Module: Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Type Checking

#include "type_eq.h"

#include "namespace.h"
#include "std_types.h"
#include "symbol.h"

bool type_eq(const typet &type1, const typet &type2, const namespacet &ns)
{
  if(type1==type2)
    return true;

  if(type1.id() == ID_symbol_type)
  {
    const symbolt &symbol = ns.lookup(to_symbol_type(type1));
    if(!symbol.is_type)
      throw "symbol "+id2string(symbol.name)+" is not a type";

    return type_eq(symbol.type, type2, ns);
  }

  if(type2.id() == ID_symbol_type)
  {
    const symbolt &symbol = ns.lookup(to_symbol_type(type2));
    if(!symbol.is_type)
      throw "symbol "+id2string(symbol.name)+" is not a type";

    return type_eq(type1, symbol.type, ns);
  }

  return false;
}
