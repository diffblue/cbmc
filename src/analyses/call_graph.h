/*******************************************************************\

Module: Function Call Graphs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_CALL_GRAPH_H
#define CPROVER_ANALYSES_CALL_GRAPH_H

#include <iosfwd>
#include <map>
#include <vector>
#include <unordered_set>

#include <goto-programs/goto_functions.h>

class call_grapht
{
public:
  call_grapht();
  explicit call_grapht(const goto_functionst &);

  void output_dot(std::ostream &out) const;
  void output(std::ostream &out) const;
  void output_xml(std::ostream &out) const;

  typedef std::multimap<irep_idt, irep_idt> grapht;
  grapht graph;

  void swap(call_grapht &other);

  void add(const irep_idt &caller, const irep_idt &callee);

  /**
   * The type provides a mapping from edges of the call-graph to particular
   * instructions in the caller GOTO programs, where the calls are performed.
   */
  typedef std::map<
            std::pair<irep_idt, irep_idt>,
            std::vector<goto_programt::instructionst::const_iterator> >
          map_from_edges_to_call_locationst;

  const map_from_edges_to_call_locationst &
  get_map_from_edges_to_call_locations() const
  { return map_from_edges_to_call_locations; }

  void add(const irep_idt &caller, const irep_idt &callee,
           const map_from_edges_to_call_locationst::mapped_type &call_sites);
protected:
  void add(const irep_idt &function,
           const goto_programt &body);

public:
  /**
   * Each element of the call graph is a pair where the first element is a
   * name of a caller function and the second element is the name of a called
   * function. So, an iterator to any such element is actually an iterator to
   * an edge of the call graph.
   */
  typedef grapht::const_iterator call_edge_iteratort;

  /**
   * Since a call graph is implemented as a multimap, we use ranges
   * of call graph edges to represent out-edges from a node (a function)
   */
  typedef
    std::pair<call_edge_iteratort, call_edge_iteratort> call_edges_ranget;

  /**
   * It returns a range of edges represented by a pair of iterators. The
   * first iterator refers to the first edge in the range and the second
   * iterator the end of the range (that edge does NOT belong to the range).
   *
   * Usage:
   *  const irep_idt caller_name = "foo";
   *  const call_grapht::call_edges_ranget range =
   *      my_call_graph.out_edges(caller_name);
   *  std::cout << "Callees of " << caller_name << " are: ";
   *  for (auto it = range.first; it != range.second; ++it)
   *    std::cout << it->second << ", ";
   */
  call_edges_ranget out_edges(const irep_idt &caller) const;

private:
  map_from_edges_to_call_locationst map_from_edges_to_call_locations;
};

/*******************************************************************\

Function: inverted_partial_topological_order

  Inputs: See purpose

 Outputs: See purpose

 Purpose:

For DAG call graphs it computes an inverted topological order of all
functions in the call graph. Otherwise, it computes only a partial
inverted topological order (all loops are broken at some (randomly)
chosen edge to get a DAG). The topolocical order is stored in the
'output' vector.

Since the algorithm is implemented using DFS, those 'breaks' are
implemented naturally by a set of processed (vidited) functions.

The function actually performs only one DFS from a passed 'start_function'.
So, to get whole inverted (partial) topological order of all functions in
the call graph, this function has to be called for all functions in the
program.

NOTE: The order is 'inverted'. It means that

Typical usage:
 // Let's assume there is 'goto_modelt GM' and 'call_grapht CG'
 std::vector<irep_idt>  result; // Here we will store the topological order.
 {
   std::unordered_set<irep_idt, dstring_hash>  processed;
   for (const auto &elem : GM.goto_functions.function_map)
     partial_topological_order(CG, elem.first, processed, result);
   // Now we reverse the result to get the classic (partial)
   // topological order instead of the inverted one.
   std::reverse(result.begin(), result.end());
 }
 std::cout << "A (partial) topological order of my call graph is: ";
 for (const irep_idt &fn_name : result)
   std::cout << fn_name << ", ";

\*******************************************************************/
void inverted_partial_topological_order(
  const call_grapht &call_graph,
  const irep_idt &start_function,
  std::unordered_set<irep_idt, dstring_hash> &processed_functions,
  std::vector<irep_idt> &output);

void get_inverted_topological_order(
  const call_grapht &call_graph,
  const goto_functionst &functions,
  std::vector<irep_idt> &output);

bool exists_direct_call(
  const call_grapht &call_graph,
  const irep_idt &caller,
  const irep_idt &callee);

bool exists_direct_or_indirect_call(
  const call_grapht &call_graph,
  const irep_idt &caller,
  const irep_idt &callee,
  std::unordered_set<irep_idt, dstring_hash> &ignored_functions);

bool exists_direct_or_indirect_call(
  const call_grapht &call_graph,
  const irep_idt &caller,
  const irep_idt &callee);

void compute_inverted_call_graph(
  const call_grapht &original_call_graph,
  call_grapht &output_inverted_call_graph);

void find_leaves_below_function(
  const call_grapht &call_graph,
  const irep_idt &function,
  std::unordered_set<irep_idt, dstring_hash> &to_avoid,
  std::unordered_set<irep_idt, dstring_hash> &output);

void find_leaves_below_function(
  const call_grapht &call_graph,
  const irep_idt &function,
  std::unordered_set<irep_idt, dstring_hash> &output);

void find_direct_or_indirect_callees_of_function(
  const call_grapht &call_graph,
  const irep_idt &function,
  std::unordered_set<irep_idt, dstring_hash> &output);

void find_nearest_common_callees(
  const call_grapht &call_graph,
  const std::set<irep_idt> &functions,
  std::set<irep_idt> &output);

/**
 * The "callee" must be a DIRECT callee of the "caller" in the "call_graph".
 */
inline const std::vector<goto_programt::instructionst::const_iterator> &
get_call_sites(
  call_grapht const&  call_graph,
  irep_idt const&  caller,
  irep_idt const&  callee)
{
  return call_graph.get_map_from_edges_to_call_locations().at({caller, callee});
}

#endif // CPROVER_ANALYSES_CALL_GRAPH_H
