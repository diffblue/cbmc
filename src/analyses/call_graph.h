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

  /**
   * It writes this into the passed stream in the Graphviz's DOT format.
   * The method accepts also functions, because the callgraph does not
   * store funtions (nodes). It only stores edges (from caller to callee).
   * So, the resulting graph would not show not-called functions.
   */
  void output_dot(goto_functionst const&  functions, std::ostream &out) const;

  void output(std::ostream &out) const;
  void output_xml(std::ostream &out) const;

  typedef std::multimap<irep_idt, irep_idt> grapht;
  grapht graph;

  void add(const irep_idt &caller, const irep_idt &callee);

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
  typedef grapht::const_iterator  call_edge_iteratort;

  /**
   * Since a call graph is implemented as a multimap, we use ranges
   * of call graph edges to represent out-edges from a node (a function)
   */
  typedef std::pair<call_edge_iteratort,call_edge_iteratort>  call_edges_ranget;

  /**
   * It returns a range of edges represented by a pair of iterators. The
   * first iterator refers to the first edge in the range and the second
   * iterator the end of the range (that edge does NOT belong to the range).
   *
   * Usage:
   *  irep_idt const  caller_name = "foo";
   *  call_grapht::call_edges_ranget const  range =
   *      my_call_graph.out_edges(caller_name);
   *  std::cout << "Callees of " << caller_name << " are: ";
   *  for (auto  it = range.first; it != range.second; ++it)
   *    std::cout << it->second << ", ";
   */
  call_edges_ranget  out_edges(irep_idt const&  caller) const;
};

/**
 * For DAG call graphs it computes an inverted topological order of all
 * functions in the call graph. Otherwise, it computes only a partial
 * inverted topological order (all loops are broken at some (randomly)
 * chosen edge to get a DAG). The topolocical order is stored in the
 * 'output' vector.
 *
 * Since the algorithm is implemented using DFS, those 'breaks' are
 * implemented naturally by a set of processed (vidited) functions.
 *
 * The function actually performs only one DFS from a passed 'start_function'.
 * So, to get whole inverted (partial) topological order of all functions in
 * the call graph, this function has to be called for all functions in the
 * program.
 *
 * NOTE: The order is 'inverted'. It means that
 *
 * Typical usage:
 *  // Let's assume there is 'goto_modelt GM' and 'call_grapht CG'
 *  std::vector<irep_idt>  result; // Here we will store the topological order.
 *  {
 *    std::unordered_set<irep_idt,dstring_hash>  processed;
 *    for (auto const&  elem : GM.goto_functions.function_map)
 *      partial_topological_order(CG,elem.first,processed,result);
 *    // Now we reverse the result to get the classic (partial)
 *    // topological order instead of the inverted one.
 *    std::reverse(result.begin(),result.end());
 *  }
 *  std::cout << "A (partial) topological order of my call graph is: ";
 *  for (irep_idt const&  fn_name : result)
 *    std::cout << fn_name << ", ";
 */
void  inverted_partial_topological_order(
    call_grapht const&  call_graph,
    irep_idt const&  start_function,
    std::unordered_set<irep_idt,dstring_hash>&  processed_functions,
    std::vector<irep_idt>&  output
    );


#endif // CPROVER_ANALYSES_CALL_GRAPH_H
