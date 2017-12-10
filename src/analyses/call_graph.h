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

class call_grapht
{
public:
  explicit call_grapht(bool collect_callsites=false);
  explicit call_grapht(const goto_modelt &, bool collect_callsites=false);
  explicit call_grapht(const goto_functionst &, bool collect_callsites=false);

  // These two constructors build a call graph restricted to functions
  // reachable from the given root.
  call_grapht(
    const goto_modelt &model,
    const irep_idt &root,
    bool collect_callsites);
  call_grapht(
    const goto_functionst &functions,
    const irep_idt &root,
    bool collect_callsites);

  void output_dot(std::ostream &out) const;
  void output(std::ostream &out) const;
  void output_xml(std::ostream &out) const;

  typedef std::multimap<irep_idt, irep_idt> grapht;
  typedef std::pair<irep_idt, irep_idt> edget;
  typedef goto_programt::const_targett locationt;
  typedef std::set<locationt> locationst;
  typedef std::map<edget, locationst> callsitest;

  grapht graph;
  callsitest callsites;

  void add(const irep_idt &caller, const irep_idt &callee);
  void add(const irep_idt &caller, const irep_idt &callee, locationt callsite);
  call_grapht get_inverted() const;

  struct edge_with_callsitest
  {
    locationst callsites;
  };

  struct function_nodet:public graph_nodet<edge_with_callsitest>
  {
    irep_idt function;
  };

  /// Directed graph representation of this call graph
  class directed_grapht : public ::grapht<function_nodet>
  {
    friend class call_grapht;

    /// Maps function names onto node indices
    std::unordered_map<irep_idt, node_indext, irep_id_hash> nodes_by_name;

  public:
    /// Find the graph node by function name
    /// \param function: function to find
    /// \return none if function is not in this graph, or some index otherwise.
    optionalt<node_indext> get_node_index(const irep_idt &function) const;

    /// Type of the node name -> node index map.
    typedef
      std::unordered_map<irep_idt, node_indext, irep_id_hash> nodes_by_namet;

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
