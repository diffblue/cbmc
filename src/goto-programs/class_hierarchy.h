/*******************************************************************\

Module: Class Hierarchy

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

/// \file
/// Class Hierarchy

#ifndef CPROVER_GOTO_PROGRAMS_CLASS_HIERARCHY_H
#define CPROVER_GOTO_PROGRAMS_CLASS_HIERARCHY_H

#include <iosfwd>
#include <map>
#include <unordered_map>

#include <util/graph.h>
#include <util/irep.h>
#include <util/ui_message.h>

// clang-format off
#define OPT_SHOW_CLASS_HIERARCHY \
  "(show-class-hierarchy)"

#define HELP_SHOW_CLASS_HIERARCHY \
  " --show-class-hierarchy       show the class hierarchy\n"
// clang-format on

class symbol_tablet;
class json_stream_arrayt;
class message_handlert;

class class_hierarchyt
{
public:
  typedef std::vector<irep_idt> idst;

  class entryt
  {
  public:
    idst parents, children;
    bool is_abstract;
  };

  typedef std::map<irep_idt, entryt> class_mapt;
  class_mapt class_map;

  void operator()(const symbol_tablet &);

  // transitively gets all children
  idst get_children_trans(const irep_idt &id) const
  {
    idst result;
    get_children_trans_rec(id, result);
    return result;
  }

  // transitively gets all parents
  idst get_parents_trans(const irep_idt &id) const
  {
    idst result;
    get_parents_trans_rec(id, result);
    return result;
  }

  void output(std::ostream &, bool children_only) const;
  void output_dot(std::ostream &) const;
  void output(json_stream_arrayt &, bool children_only) const;

protected:
  void get_children_trans_rec(const irep_idt &, idst &) const;
  void get_parents_trans_rec(const irep_idt &, idst &) const;
};

/// Class hierarchy graph node: simply contains a class identifier.
class class_hierarchy_graph_nodet : public graph_nodet<empty_edget>
{
public:
  /// Class ID for this node
  irep_idt class_identifier;
};

/// Class hierarchy, represented using grapht and therefore suitable for use
/// with generic graph algorithms.
class class_hierarchy_grapht : public grapht<class_hierarchy_graph_nodet>
{
public:
  /// Maps class identifiers onto node indices
  typedef std::unordered_map<irep_idt, node_indext> nodes_by_namet;

  void populate(const symbol_tablet &);

  /// Get map from class identifier to node index
  /// \return map from class identifier to node index
  const nodes_by_namet &get_nodes_by_class_identifier() const
  {
    return nodes_by_name;
  }

private:
  /// Maps class identifiers onto node indices
  nodes_by_namet nodes_by_name;
};

/// Output the class hierarchy
/// \param hierarchy: the class hierarchy to be printed
/// \param message_handler: the message handler
/// \param ui: the UI format
/// \param children_only: print the children only and do not print the parents
void show_class_hierarchy(
  const class_hierarchyt &hierarchy,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  bool children_only = false);

#endif // CPROVER_GOTO_PROGRAMS_CLASS_HIERARCHY_H
