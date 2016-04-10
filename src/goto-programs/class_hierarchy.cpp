/*******************************************************************\

Module: Class Hierarchy

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

#include <util/std_types.h>

#include "class_hierarchy.h"

/*******************************************************************\

Function: class_hierarchyt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void class_hierarchyt::operator()(const symbol_tablet &symbol_table)
{
  forall_symbols(it, symbol_table.symbols)
  {
    if(it->second.is_type && it->second.type.id()==ID_struct)
    {
      const struct_typet &struct_type=
        to_struct_type(it->second.type);

      const struct_typet::componentst &components=
        struct_type.components();
      
      if(components.empty()) continue;
      
      irep_idt name=components.front().get_name();
      
      if(name.empty()) continue;
      
      if(name[0]!='@') continue;
      
      if(components.front().type().id()!=ID_symbol) continue;
      
      irep_idt parent=
        to_symbol_type(components.front().type()).get_identifier();
      
      class_map[parent].children.push_back(it->first);
      class_map[it->first].parent=parent;
    }
  }
}

/*******************************************************************\

Function: class_hierarchyt::get_children

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void class_hierarchyt::get_children(
  const irep_idt &c,
  std::vector<irep_idt> &dest) const
{
  class_mapt::const_iterator it=class_map.find(c);
  if(it==class_map.end()) return;
  const entryt &entry=it->second;
  
  for(const auto & child : entry.children)
    dest.push_back(child);

  // recursive calls
  for(const auto & child : entry.children)
    get_children(child, dest);
}

/*******************************************************************\

Function: class_hierarchyt::get_parent

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt class_hierarchyt::get_parent(const irep_idt &c) const
{
  class_mapt::const_iterator it=class_map.find(c);
  if(it==class_map.end()) return irep_idt();
  return it->second.parent;
}
