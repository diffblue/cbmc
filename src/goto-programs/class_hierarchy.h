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

#include <util/graph.h>
#include <util/namespace.h>

class class_hierarchyt
{
public:
  typedef std::vector<irep_idt> idst;

  class entryt
  {
  public:
    idst parents, children;
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

  void output(std::ostream &) const;
  void output_dot(std::ostream &) const;

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
  typedef std::unordered_map<irep_idt, node_indext, irep_id_hash>
    nodes_by_namet;

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

#endif // CPROVER_GOTO_PROGRAMS_CLASS_HIERARCHY_H
