/*******************************************************************\

Module: Class Hierarchy

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

/// \file
/// Class Hierarchy

#include "class_hierarchy.h"

#include <iterator>
#include <ostream>

#include <util/json_stream.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

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
          const auto parent_node_it = nodes_by_name.find(parent);
          DATA_INVARIANT(
            parent_node_it != nodes_by_name.end(),
            "parent class not in symbol table");
          add_edge(parent_node_it->second, nodes_by_name.at(symbol_pair.first));
        }
      }
    }
  }
}

/// Helper function that converts a vector of node_indext to a vector of ids
/// that are stored in the corresponding nodes in the graph.
class_hierarchy_grapht::idst class_hierarchy_grapht::ids_from_indices(
  const std::vector<node_indext> &node_indices) const
{
  idst result;
  std::transform(
    node_indices.begin(),
    node_indices.end(),
    back_inserter(result),
    [&](const node_indext &node_index) {
      return (*this)[node_index].class_identifier;
    });
  return result;
}

/// Get all the classes that directly (i.e. in one step) inherit from class c.
/// \param c: The class to consider
/// \return A list containing ids of all direct children of c.
class_hierarchy_grapht::idst
class_hierarchy_grapht::get_direct_children(const irep_idt &c) const
{
  const node_indext &node_index = nodes_by_name.at(c);
  const auto &child_indices = get_successors(node_index);
  return ids_from_indices(child_indices);
}

/// Helper function for `get_children_trans` and `get_parents_trans`
class_hierarchy_grapht::idst class_hierarchy_grapht::get_other_reachable_ids(
  const irep_idt &c,
  bool forwards) const
{
  idst direct_child_ids;
  const node_indext &node_index = nodes_by_name.at(c);
  const auto &reachable_indices = get_reachable(node_index, forwards);
  auto reachable_ids = ids_from_indices(reachable_indices);
  // Remove c itself from the list
  // TODO Adding it first and then removing it is not ideal. It would be
  // better to define a function grapht::get_other_reachable and directly use
  // that here.
  reachable_ids.erase(
    std::remove(reachable_ids.begin(), reachable_ids.end(), c),
    reachable_ids.end());
  return reachable_ids;
}

/// Get all the classes that inherit (directly or indirectly) from class c.
/// \param c: The class to consider
/// \return A list containing ids of all classes that eventually inherit from c.
class_hierarchy_grapht::idst
class_hierarchy_grapht::get_children_trans(const irep_idt &c) const
{
  return get_other_reachable_ids(c, true);
}

/// Get all the classes that class c inherits from (directly or indirectly).
/// \param c: The class to consider
/// \return A list of class ids that c eventually inherits from.
class_hierarchy_grapht::idst
class_hierarchy_grapht::get_parents_trans(const irep_idt &c) const
{
  return get_other_reachable_ids(c, false);
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

      const irept::subt &bases = struct_type.find(ID_bases).get_sub();

      for(const auto &base : bases)
      {
        irep_idt parent = base.find(ID_type).get(ID_identifier);
        if(parent.empty())
          continue;

        class_map[parent].children.push_back(symbol_pair.first);
        class_map[symbol_pair.first].parents.push_back(parent);
      }
    }
  }
}

/// Get all the classes that class c inherits from (directly or indirectly). The
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
  ui_message_handlert &message_handler,
  bool children_only)
{
  messaget msg(message_handler);
  switch(message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    hierarchy.output(msg.result(), children_only);
    msg.result() << messaget::eom;
    break;
  case ui_message_handlert::uit::JSON_UI:
    if(msg.result().tellp() > 0)
      msg.result() << messaget::eom; // force end of previous message
    hierarchy.output(message_handler.get_json_stream(), children_only);
    break;
  case ui_message_handlert::uit::XML_UI:
    UNIMPLEMENTED;
  }
}
