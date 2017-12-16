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

#endif
