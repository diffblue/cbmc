/*******************************************************************\

Module: Class Hierarchy

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

/// \file
/// Class Hierarchy

#include "class_hierarchy.h"

#include <ostream>

#include <util/json_stream.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

/// Looks for all the struct types in the symbol table and construct a map from
/// class names to a data structure that contains lists of parent and child
/// classes for each struct type (ie class).
/// \param symbol_table: The symbol table to analyze
void class_hierarchyt::operator()(const symbol_tablet &symbol_table)
{
  for(const auto &symbol_pair : symbol_table.symbols)
  {
    if(symbol_pair.second.is_type && symbol_pair.second.type.id() == ID_struct)
    {
      const struct_typet &struct_type = to_struct_type(symbol_pair.second.type);

      class_map[symbol_pair.first].is_abstract =
        struct_type.get_bool(ID_abstract);

      const irept::subt &bases=
        struct_type.find(ID_bases).get_sub();

      for(const auto &base : bases)
      {
        irep_idt parent=base.find(ID_type).get(ID_identifier);
        if(parent.empty())
          continue;

        class_map[parent].children.push_back(symbol_pair.first);
        class_map[symbol_pair.first].parents.push_back(parent);
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
  for(const auto &symbol_pair : symbol_table.symbols)
  {
    if(symbol_pair.second.is_type && symbol_pair.second.type.id() == ID_struct)
    {
      node_indext new_node_index = add_node();
      nodes_by_name[symbol_pair.first] = new_node_index;
      (*this)[new_node_index].class_identifier = symbol_pair.first;
    }
  }

  // Add parent -> child edges:
  for(const auto &symbol_pair : symbol_table.symbols)
  {
    if(symbol_pair.second.is_type && symbol_pair.second.type.id() == ID_struct)
    {
      const class_typet &class_type = to_class_type(symbol_pair.second.type);

      for(const auto &base : class_type.bases())
      {
        const irep_idt &parent = to_symbol_type(base.type()).get_identifier();
        if(!parent.empty())
        {
          add_edge(
            nodes_by_name.at(parent), nodes_by_name.at(symbol_pair.first));
        }
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

/// Output the class hierarchy in plain text
/// \param out: the output stream
/// \param children_only: print the children only and do not print the parents
void class_hierarchyt::output(std::ostream &out, bool children_only) const
{
  for(const auto &c : class_map)
  {
    out << c.first << (c.second.is_abstract ? " (abstract)" : "") << ":\n";
    if(!children_only)
    {
      out << "  parents:\n";
      for(const auto &pa : c.second.parents)
        out << "    " << pa << '\n';
    }
    out << "  children:\n";
    for(const auto &ch : c.second.children)
      out << "    " << ch << '\n';
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

/// Output the class hierarchy in JSON format
/// \param json_stream: the output JSON stream array
/// \param children_only: print the children only and do not print the parents
void class_hierarchyt::output(
  json_stream_arrayt &json_stream,
  bool children_only) const
{
  for(const auto &c : class_map)
  {
    json_stream_objectt &json_class = json_stream.push_back_stream_object();
    json_class["name"] = json_stringt(c.first);
    json_class["isAbstract"] = jsont::json_boolean(c.second.is_abstract);
    if(!children_only)
    {
      json_stream_arrayt &json_parents =
        json_class.push_back_stream_array("parents");
      for(const auto &pa : c.second.parents)
        json_parents.push_back(json_stringt(pa));
    }
    json_stream_arrayt &json_children =
      json_class.push_back_stream_array("children");
    for(const auto &ch : c.second.children)
      json_children.push_back(json_stringt(ch));
  }
}

void show_class_hierarchy(
  const class_hierarchyt &hierarchy,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  bool children_only)
{
  messaget msg(message_handler);
  switch(ui)
  {
  case ui_message_handlert::uit::PLAIN:
    hierarchy.output(msg.result(), children_only);
    msg.result() << messaget::eom;
    break;
  case ui_message_handlert::uit::JSON_UI:
    hierarchy.output(msg.result().json_stream(), children_only);
    break;
  case ui_message_handlert::uit::XML_UI:
    UNIMPLEMENTED;
  }
}
