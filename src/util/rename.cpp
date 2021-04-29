/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "rename.h"

#include <string>

#include "namespace.h"

irep_idt
get_new_name(const irep_idt &name, const namespacet &ns, char delimiter)
{
  const symbolt *symbol;
  if(ns.lookup(name, symbol))
    return name;

  std::string prefix = id2string(name) + delimiter;

  return prefix + std::to_string(ns.smallest_unused_suffix(prefix));
}
