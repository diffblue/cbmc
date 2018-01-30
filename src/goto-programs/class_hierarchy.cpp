/*******************************************************************\

Module: Class Hierarchy

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

/// \file
/// Class Hierarchy

#include "class_hierarchy.h"

#include <ostream>

#include <util/std_types.h>
#include <util/symbol_table.h>

/// Looks for all the struct types in the symbol table and construct a map from
/// class names to a data structure that contains lists of parent and child
/// classes for each struct type (ie class).
/// \param symbol_table: The symbol table to analyze
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

/// Populate the class hierarchy graph, such that there is a node for every
/// struct type in the symbol table and an edge representing each superclass
/// <-> subclass relationship, pointing from parent to child.
/// \param symbol_table: global symbol table, which will be searched for struct
///   types.
void class_hierarchy_grapht::populate(const symbol_tablet &symbol_table)
{
  // Add nodes for all classes:
  forall_symbols(it, symbol_table.symbols)
  {
    if(it->second.is_type && it->second.type.id() == ID_struct)
    {
      node_indext new_node_index = add_node();
      nodes_by_name[it->first] = new_node_index;
      (*this)[new_node_index].class_identifier = it->first;
    }
  }

  // Add parent -> child edges:
  forall_symbols(it, symbol_table.symbols)
  {
    if(it->second.is_type && it->second.type.id() == ID_struct)
    {
      const class_typet &class_type = to_class_type(it->second.type);

      for(const auto &base : class_type.bases())
      {
        const irep_idt &parent = to_symbol_type(base.type()).get_identifier();
        if(!parent.empty())
          add_edge(nodes_by_name.at(parent), nodes_by_name.at(it->first));
      }
    }
  }
}

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

/// Get all the classes that inherit (directly or indirectly) from class c. The
/// first element(s) will be the immediate parents of c, though after this
/// the order is all the parents of the first immediate parent
/// \param c: The class to consider
/// \param [out] dest: A list of class ids that c eventually inherits from.
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

/// Output class hierarchy in Graphviz DOT format
/// \param ostr: stream to write DOT to
void class_hierarchyt::output_dot(std::ostream &ostr) const
{
  ostr << "digraph class_hierarchy {\n"
       << "  rankdir=BT;\n"
       << "  node [fontsize=12 shape=box];\n";
  for(const auto &c : class_map)
  {
    for(const auto &ch : c.second.parents)
    {
      ostr << "  \"" << c.first << "\" -> "
           << "\"" << ch << "\" "
           << " [arrowhead=\"vee\"];"
           << "\n";
    }
  }
  ostr << "}\n";
}
