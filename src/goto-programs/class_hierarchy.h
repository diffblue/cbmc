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

/// Non-graph-based representation of the class hierarchy.
/// \deprecated `class_hierarchy_grapht` is a more advanced graph-based
///   representation of the class hierarchy and its use is preferred over
///   `class_hierarchy_classt`.
/// \todo Implement missing functions from `class_hierarchyt` in
///   `class_hierarchy_grapht` so that `class_hierarchyt` can be fully replaced.
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

  class_hierarchyt() = default;
  explicit class_hierarchyt(const symbol_tablet &symbol_table)
  {
    (*this)(symbol_table);
  }
  class_hierarchyt(const class_hierarchyt &) = delete;
  class_hierarchyt &operator=(const class_hierarchyt &) = delete;

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
  typedef std::vector<irep_idt> idst;

  /// Maps class identifiers onto node indices
  typedef std::unordered_map<irep_idt, node_indext> nodes_by_namet;

  void populate(const symbol_tablet &);

  /// Get map from class identifier to node index
  /// \return map from class identifier to node index
  const nodes_by_namet &get_nodes_by_class_identifier() const
  {
    return nodes_by_name;
  }

  idst get_direct_children(const irep_idt &c) const;

  idst get_children_trans(const irep_idt &c) const;

  idst get_parents_trans(const irep_idt &c) const;

private:
  /// Maps class identifiers onto node indices
  nodes_by_namet nodes_by_name;

  idst ids_from_indices(const std::vector<node_indext> &nodes) const;

  idst get_other_reachable_ids(const irep_idt &c, bool forwards) const;
};

/// Output the class hierarchy
/// \param hierarchy: the class hierarchy to be printed
/// \param message_handler: the message handler
/// \param children_only: print the children only and do not print the parents
void show_class_hierarchy(
  const class_hierarchyt &hierarchy,
  ui_message_handlert &message_handler,
  bool children_only = false);

#endif // CPROVER_GOTO_PROGRAMS_CLASS_HIERARCHY_H
