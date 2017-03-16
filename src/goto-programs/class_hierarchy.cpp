/*******************************************************************\

Module: Class Hierarchy

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

#include <ostream>

#include <util/std_types.h>
#include <util/symbol_table.h>

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

      const irept::subt &bases=
        struct_type.find(ID_bases).get_sub();

      for(const auto &base : bases)
      {
        irep_idt parent=base.find(ID_type).get(ID_identifier);
        if(parent.empty())
          continue;

        class_map[parent].children.push_back(it->first);
        class_map[it->first].parents.push_back(parent);
      }
    }
  }
}

/*******************************************************************\

Function: class_hierarchyt::get_children_trans_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void class_hierarchyt::get_children_trans_rec(
  const irep_idt &c,
  idst &dest) const
{
  class_mapt::const_iterator it=class_map.find(c);
  if(it==class_map.end())
    return;
  const entryt &entry=it->second;

  for(const auto &child : entry.children)
    dest.push_back(child);

  // recursive calls
  for(const auto &child : entry.children)
    get_children_trans_rec(child, dest);
}

/*******************************************************************\

Function: class_hierarchyt::get_parents_trans_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void class_hierarchyt::get_parents_trans_rec(
  const irep_idt &c,
  idst &dest) const
{
  class_mapt::const_iterator it=class_map.find(c);
  if(it==class_map.end())
    return;
  const entryt &entry=it->second;

  for(const auto &child : entry.parents)
    dest.push_back(child);

  // recursive calls
  for(const auto &child : entry.parents)
    get_parents_trans_rec(child, dest);
}

/*******************************************************************\

Function: class_hierarchyt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void class_hierarchyt::output(std::ostream &out) const
{
  for(const auto &c : class_map)
  {
    for(const auto &pa : c.second.parents)
      out << "Parent of " << c.first << ": "
          << pa << '\n';

    for(const auto &ch : c.second.children)
      out << "Child of " << c.first << ": "
          << ch << '\n';
  }
}

/*******************************************************************\

Function: output_dot

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &output_dot(std::ostream &ostr, const class_hierarchyt &hierarchy)
{
  ostr << "digraph call_graph {\n"
       << "  rankdir=BT;\n"
       << "  node [fontsize=12 shape=box];\n";
  for(const auto &c : hierarchy.class_map)
    for(const auto &ch : c.second.parents)
      ostr << "  \"" << c.first << "\" -> "
           << "\"" << ch << "\" "
           << " [arrowhead=\"vee\"];"
           << "\n";
  ostr << "}\n";
  return ostr;
}
