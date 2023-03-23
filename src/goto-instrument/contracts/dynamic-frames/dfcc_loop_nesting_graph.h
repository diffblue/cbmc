/*******************************************************************\

Module: Dynamic frame condition checking

Author: Qinheping Hu, qinhh@amazon.com

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

/// \file
/// Builds a graph describing how loops are nested in a GOTO program.

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LOOP_NESTING_GRAPH_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LOOP_NESTING_GRAPH_H

#include <util/graph.h>

#include <goto-instrument/loop_utils.h>

class messaget;

/// A graph node that stores information about a natural loop.
struct dfcc_loop_nesting_graph_nodet : public graph_nodet<empty_edget>
{
public:
  dfcc_loop_nesting_graph_nodet(
    const goto_programt::targett &head,
    const goto_programt::targett &latch,
    const loopt &instructions);

  /// Loop head instruction
  goto_programt::targett head;

  /// Loop latch instruction
  goto_programt::targett latch;

  /// Set of loop instructions
  loopt instructions;
};

typedef grapht<dfcc_loop_nesting_graph_nodet> dfcc_loop_nesting_grapht;

/// \brief Builds a graph instance describing the nesting structure of natural
/// loops in the given \p goto_program.
/// A loop is considered nested in an outer loop if its head and its latch are
/// both found in the instructions of the outer loop.
dfcc_loop_nesting_grapht
build_loop_nesting_graph(goto_programt &goto_program, messaget &log);
#endif
