/*******************************************************************\

Module: Pretty name generation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "identifier.h"
#include "pretty_names.h"
#include "namespace.h"
#include "symbol.h"

/*******************************************************************\

Function: pretty_namest::get_pretty_names

  Inputs:

 Outputs:

 Purpose: make displayed variable names unique, but
          as short as possible

\*******************************************************************/

void pretty_namest::get_pretty_names(
  const symbolst &symbols,
  const namespacet &ns)
{
  symbolst todo(symbols);

  // first try base names
  std::multiset<irep_idt> names;

  for(symbolst::const_iterator
      it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    const symbolt *symbol;
    if(ns.lookup(*it, symbol))
      pretty_map[*it]=*it;
    else
    {
      names.insert(symbol->base_name);
      pretty_map[*it]=symbol->base_name;
    }
  }

  std::map<irep_idt, unsigned> name_components;

  // find collisions

  while(1)
  {
    std::set<irep_idt> collisions;

    for(symbolst::const_iterator it=symbols.begin();
        it!=symbols.end(); it++)
      if(names.count(pretty_map[*it])>=2)
        collisions.insert(*it);

    if(collisions.empty())
      return; // done

    names.clear();

    for(std::set<irep_idt>::const_iterator it=collisions.begin();
        it!=collisions.end(); it++)
    {
      unsigned no_components=(++name_components[*it]);

      identifiert id(id2string(*it));

      if(no_components>=id.components.size())
        pretty_map[*it]=*it;
      else
      {
        while(no_components<id.components.size())
          id.components.erase(
            id.components.begin(),
            id.components.begin()+(id.components.size()-no_components));

        std::string new_name=id.as_string();

        names.insert(new_name);
        pretty_map[*it]=new_name;      
      }
    }
  }
}

/*******************************************************************\

Function: pretty_namest::pretty_names

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irep_idt &pretty_namest::pretty_name(
  const irep_idt &identifier) const
{
  pretty_mapt::const_iterator it=pretty_map.find(identifier);
  if(it==pretty_map.end()) return identifier;
  return it->second;
}
