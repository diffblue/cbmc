/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Call Graph

#ifndef CPROVER_ANALYSES_CALL_GRAPH_H
#define CPROVER_ANALYSES_CALL_GRAPH_H

#include <iosfwd>
#include <map>
#include <unordered_set>

#include <goto-programs/goto_model.h>

#include <util/irep.h>
#include <util/graph.h>
#include <util/numbering.h>


/// \brief Function call graph: each node represents a function
/// in the GOTO model, a directed edge from A to B indicates
/// that function A calls function B.
/// Inherits from grapht to allow forward and
/// backward traversal of the function call graph
struct call_graph_nodet: public graph_nodet<empty_edget>
{
  typedef graph_nodet<empty_edget>::edget edget;
  typedef graph_nodet<empty_edget>::edgest edgest;

  irep_idt function_name;
  bool visited = false;
};

class call_grapht: public grapht<call_graph_nodet>
{
public:
  call_grapht();
  explicit call_grapht(const goto_modelt &);
  explicit call_grapht(const goto_functionst &);

  void add(const irep_idt &caller, const irep_idt &callee);
  void output_xml(std::ostream &out) const;

  /// \return the inverted call graph
  call_grapht get_inverted() const;

  /// \brief get the names of all functions reachable from a start function
  /// \param start  name of initial function
  /// \return set of all names of the reachable functions
  std::unordered_set<irep_idt, irep_id_hash>
      reachable_functions(irep_idt start);

  /// \brief Function returns the shortest path on the function call graph
  /// between a source and a destination function
  /// \param src  name of the starting function
  /// \param dest name of the destination function
  /// \return list of function names on the shortest path between src and dest
  std::list<irep_idt>shortest_function_path(irep_idt src, irep_idt dest);

  /// \brief get the names of all functions reachable from a list of functions
  /// within N function call steps.
  /// \param function_list  list of functions to start from.
  /// Functions reachable within
  /// N function call steps are appended to this list
  /// \param steps  number of function call steps
  void reachable_within_n_steps(std::size_t steps,
      std::unordered_set<irep_idt, irep_id_hash> &function_list);


  /// get the index of the node that corresponds to a function name
  /// \param[in] function_name function_name passed by reference
  /// \param[out] n variable for the node index to be written to
  /// \return true if a node with the given function name exists,
  /// false if it does not exist
  bool get_node_index(const irep_idt& function_name, node_indext &n) const
  {
    for(node_indext idx = 0; idx < nodes.size(); idx++)
    {
      if(nodes[idx].function_name == function_name)
      {
        n = idx;
        return true;
      }
    }
    return false;
  }

  /// \brief get a list of functions called by a function
  /// \param function_name   the irep_idt of the function
  /// \return an unordered set of all functions called by function_name
  std::unordered_set<irep_idt, irep_id_hash> get_successors(
      const irep_idt& function_name) const
  {
    std::unordered_set<irep_idt, irep_id_hash> result;
    node_indext function_idx;
    if(!get_node_index(function_name, function_idx))
      return result;

    for(const auto &o : nodes[function_idx].out)
      result.insert(nodes[o.first].function_name);
    return result;
  }


protected:
  void output_dot_node(std::ostream &out, node_indext n) const override;
  void output_xml_node(std::ostream &out, node_indext n) const;
  numbering<irep_idt> node_numbering;
  void add(const irep_idt &function,
           const goto_programt &body);
};

#endif // CPROVER_ANALYSES_CALL_GRAPH_H
