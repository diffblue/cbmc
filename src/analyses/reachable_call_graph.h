/*******************************************************************\

Module: Reachable Call Graphs

Author:

\*******************************************************************/

/// \file
/// Reachable Call Graphs
/// Constructs a call graph only from the functions reachable from a given
/// entry point, or the goto_functions.entry_point if none is given.

#ifndef CPROVER_ANALYSES_REACHABLE_CALL_GRAPH_H
#define CPROVER_ANALYSES_REACHABLE_CALL_GRAPH_H

#include "call_graph.h"

class reachable_call_grapht: public call_grapht
{
public:
  explicit reachable_call_grapht(const goto_modelt &);

  /// \brief performs a backwards slice on a reachable call graph
  /// and returns an unordered set of all functions between the initial
  /// function and the destination function, i.e., a cone of influence
  /// \param destination_function   name of destination function
  /// \return unordered set of function names
  std::unordered_set<irep_idt, irep_id_hash>
  backward_slice(irep_idt destination_function);
protected:
  void build(const goto_functionst &);
  void build(const goto_functionst &, irep_idt start_function);
};

#endif /* SRC_ANALYSES_REACHABLE_CALL_GRAPH_H_ */
