/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Call Graphs

#ifndef CPROVER_ANALYSES_CALL_GRAPH_H
#define CPROVER_ANALYSES_CALL_GRAPH_H

#include <iosfwd>
#include <map>

#include <goto-programs/goto_model.h>
#include <util/graph.h>

/// A call graph (https://en.wikipedia.org/wiki/Call_graph) for a GOTO model
/// or GOTO functions collection.
///
/// The public constructors build a complete call graph, while
/// \ref call_grapht::create_from_root_function can be used to create a partial
/// call graph rooted at a particular function.
///
/// The graph is stored as a `std::multimap`, and this class only provides basic
/// tools to construct and query graphs, but it can be exported to a \ref grapht
/// and thus processed using the full graph algorithms library using the
/// \ref get_directed_graph method. See also \ref call_graph_helpers.h for
/// helper methods that work with such grapht-derived call graphs.
///
/// The graph may optionally collect (and export) the callsite associated with
/// each edge; pass the `collect_callsites` parameter to a constructor if you
/// want this functionality, and query the \ref call_grapht::callsites
/// collection.
class call_grapht
{
public:
  explicit call_grapht(bool collect_callsites=false);
  explicit call_grapht(const goto_modelt &, bool collect_callsites=false);
  explicit call_grapht(const goto_functionst &, bool collect_callsites=false);

  // These two functions build a call graph restricted to functions
  // reachable from the given root.

  static call_grapht create_from_root_function(
    const goto_modelt &model,
    const irep_idt &root,
    bool collect_callsites)
  {
    return call_grapht(model, root, collect_callsites);
  }

  static call_grapht create_from_root_function(
    const goto_functionst &functions,
    const irep_idt &root,
    bool collect_callsites)
  {
    return call_grapht(functions, root, collect_callsites);
  }

  // Constructors used to implement the above:

private:
  call_grapht(
    const goto_modelt &model,
    const irep_idt &root,
    bool collect_callsites);
  call_grapht(
    const goto_functionst &functions,
    const irep_idt &root,
    bool collect_callsites);

public:

  void output_dot(std::ostream &out) const;
  void output(std::ostream &out) const;
  void output_xml(std::ostream &out) const;

  /// Type of the nodes in the call graph.
  typedef std::unordered_set<irep_idt, irep_id_hash> nodest;

  /// Type of the edges in the call graph. Note parallel edges (e.g. A having
  /// two callsites both targeting B) result in multiple graph edges.
  typedef std::multimap<irep_idt, irep_idt> edgest;

  /// Type of a call graph edge in `edgest`
  typedef std::pair<irep_idt, irep_idt> edget;

  /// Type of a callsite stored in member `callsites`
  typedef goto_programt::const_targett locationt;

  /// Type of a set of callsites
  typedef std::set<locationt> locationst;

  /// Type mapping from call-graph edges onto the set of call instructions
  /// that make that call.
  typedef std::map<edget, locationst> callsitest;

  /// Call graph, including duplicate key-value pairs when there are parallel
  /// edges (see `grapht` documentation). This representation is retained for
  /// backward compatibility; use `get_directed_graph()` to get a generic
  /// directed graph representation that provides more graph algorithms
  /// (shortest path, SCCs and so on).
  edgest edges;
  nodest nodes;

  /// Map from call-graph edges to a set of callsites that make the given call.
  callsitest callsites;

  void add(const irep_idt &caller, const irep_idt &callee);
  void add(const irep_idt &caller, const irep_idt &callee, locationt callsite);

  call_grapht get_inverted() const;

  /// Edge of the directed graph representation of this call graph
  struct edge_with_callsitest
  {
    /// Callsites responsible for this graph edge. Will be empty if
    /// `collect_callsites` was not set at `call_grapht` construction time.
    locationst callsites;
  };

  /// Node of the directed graph representation of this call graph
  struct function_nodet : public graph_nodet<edge_with_callsitest>
  {
    /// Function name
    irep_idt function;
  };

  /// Directed graph representation of this call graph
  class directed_grapht : public ::grapht<function_nodet>
  {
    friend class call_grapht;

    /// Maps function names onto node indices
    std::unordered_map<irep_idt, node_indext> nodes_by_name;

  public:
    /// Find the graph node by function name
    /// \param function: function to find
    /// \return none if function is not in this graph, or some index otherwise.
    optionalt<node_indext> get_node_index(const irep_idt &function) const;

    /// Type of the node name -> node index map.
    typedef std::unordered_map<irep_idt, node_indext> nodes_by_namet;

    /// Get the node name -> node index map
    /// \return node-by-name map
    const nodes_by_namet &get_nodes_by_name() const
    {
      return nodes_by_name;
    }
  };

  directed_grapht get_directed_graph() const;

protected:
  void add(const irep_idt &function,
           const goto_programt &body);
private:
  bool collect_callsites;
  std::string format_callsites(const edget &edge) const;
};

#endif // CPROVER_ANALYSES_CALL_GRAPH_H
