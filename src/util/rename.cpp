/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "rename.h"

#include <string>

#include "symbol.h"
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
