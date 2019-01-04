/*******************************************************************\

Module: Function Call Graph Helpers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

/// \file
/// Function Call Graph Helpers

#ifndef CPROVER_ANALYSES_CALL_GRAPH_HELPERS_H
#define CPROVER_ANALYSES_CALL_GRAPH_HELPERS_H

#include "call_graph.h"

// These are convenience functions for working with the directed graph
// representation of a call graph, obtained via
// `call_grapht::get_directed_graph`. Usually function names must be mapped
// to and from node indices, as in `graph.get_node_index("f")`, or
// `graph[node_index].function`; these helpers include the translation for
// convenience.

/// Get functions directly callable from a given function
/// \param graph: call graph
/// \param function: function to query
/// \return set of called functions
std::set<irep_idt> get_callees(
  const call_grapht::directed_grapht &graph, const irep_idt &function);

/// Get functions that call a given function
/// \param graph: call graph
/// \param function: function to query
/// \return set of caller functions
std::set<irep_idt> get_callers(
  const call_grapht::directed_grapht &graph, const irep_idt &function);

/// Get functions reachable from a given function
/// \param graph: call graph
/// \param function: function to query
/// \return set of reachable functions, including `function`
std::set<irep_idt> get_reachable_functions(
  const call_grapht::directed_grapht &graph, const irep_idt &function);

/// Get functions that can reach a given function
/// \param graph: call graph
/// \param function: function to query
/// \return set of functions that can reach the target, including `function`
std::set<irep_idt> get_reaching_functions(
  const call_grapht::directed_grapht &graph, const irep_idt &function);

/// Get either callers or callees reachable from a given
/// list of functions within N steps
/// \param graph: call graph
/// \param start_functions: set of start functions
/// \param n: number of steps to consider
/// \return set of functions that can be reached from the start function
///   including the start function
std::set<irep_idt> get_functions_reachable_within_n_steps(
  const call_grapht::directed_grapht &graph,
  const std::set<irep_idt> &start_functions,
  std::size_t n);

/// Get either callers or callees reachable from a given
/// list of functions within N steps
/// \param graph: call graph
/// \param start_function: single start function
/// \param n: number of steps to consider
/// \return set of functions that can be reached from the start function
///   including the start function
std::set<irep_idt> get_functions_reachable_within_n_steps(
  const call_grapht::directed_grapht &graph,
  const irep_idt &start_function,
  std::size_t n);

/// Get list of functions on the shortest path between two functions
/// \param graph: call graph
/// \param src: function to start from
/// \param dest: function to reach
/// \return list of functions on shortest path
std::list<irep_idt> get_shortest_function_path(
  const call_grapht::directed_grapht &graph,
  const irep_idt &src,
  const irep_idt &dest);

/// Disconnects all functions in the call graph that are unreachable from
/// a given start function.
/// Removing nodes requires re-indexing, so instead we disconnect them, removing
/// all in and out edges from those nodes.
/// This speeds up backwards reachability.
/// \param graph: call graph
/// \param function: start function
void disconnect_unreachable_functions(
  call_grapht::directed_grapht &graph,
  const irep_idt &function);

#endif
