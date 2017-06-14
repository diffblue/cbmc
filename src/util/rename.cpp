/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <algorithm>

#include "rename.h"
#include "symbol.h"
#include "expr.h"
#include "namespace.h"

/// automated variable renaming
/// \par parameters: symbol to be renamed, namespace
/// \return new symbol
void get_new_name(symbolt &symbol, const namespacet &ns)
{
  get_new_name(symbol.name, ns);
}

/// automated variable renaming
/// \par parameters: symbol to be renamed, namespace
/// \return new symbol
void get_new_name(irep_idt &new_name, const namespacet &ns)
{
  const symbolt *symbol;
  if(ns.lookup(new_name, symbol))
    return;

  std::string prefix=id2string(new_name)+"_";

  new_name=prefix+std::to_string(ns.get_max(prefix)+1);
}

/// automated variable renaming
/// \par parameters: expression, old name, new name
/// \return modifies the expression returns false iff something was renamed
bool rename(exprt &expr, const irep_idt &old_name,
            const irep_idt &new_name)
{
  bool result=true;

  if(expr.id()==ID_symbol)
  {
    if(expr.get(ID_identifier)==old_name)
    {
      expr.set(ID_identifier, new_name);
      result=false;
    }
  }
  else
  {
    if(expr.id()==ID_address_of)
    {
      // TODO
    }
    else
      Forall_operands(it, expr)
        if(!rename(*it, old_name, new_name))
          result=false;
  }

  return result;
}
