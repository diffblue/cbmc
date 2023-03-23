/*******************************************************************\

Module: Dynamic frame condition checking

Author: Qinheping Hu, qinhh@amazon.com

Author: Remi Delmas, delmasrd@amazon.com

Date: March 2023

\*******************************************************************/

#include "dfcc_loop_nesting_graph.h"

#include <util/invariant.h>
#include <util/message.h>

dfcc_loop_nesting_graph_nodet::dfcc_loop_nesting_graph_nodet(
  const goto_programt::targett &head,
  const goto_programt::targett &latch,
  const loopt &instructions)
  : head(head), latch(latch), instructions(instructions)
{
}

/// \pre Loop normal form properties must hold.
dfcc_loop_nesting_grapht
build_loop_nesting_graph(goto_programt &goto_program, messaget &log)
{
  natural_loops_mutablet natural_loops(goto_program);
  dfcc_loop_nesting_grapht loop_nesting_graph;
  // Add a node per natural loop
  for(auto &loop : natural_loops.loop_map)
  {
    auto loop_head = loop.first;
    auto &loop_instructions = loop.second;

    if(loop_instructions.size() <= 1)
    {
      // ignore single instruction loops of the form
      // LOOP: goto LOOP;
      continue;
    }

    // Find the instruction that jumps back to `loop_head` and has the
    // highest GOTO location number, define it as the latch.
    auto loop_latch = loop_head;
    for(const auto &t : loop_instructions)
    {
      if(
        t->is_goto() && t->get_target() == loop_head &&
        t->location_number > loop_latch->location_number)
        loop_latch = t;
    }

    DATA_INVARIANT(loop_latch != loop_head, "Natural loop latch is found");

    loop_nesting_graph.add_node(loop_head, loop_latch, loop_instructions);
  }

  // Add edges to the graph, pointing from inner loop to outer loops.
  // An `inner` will be considered nested in `outer` iff both its head
  // and latch instructions are instructions of `outer`.
  for(size_t outer = 0; outer < loop_nesting_graph.size(); ++outer)
  {
    const auto &outer_instructions = loop_nesting_graph[outer].instructions;

    for(size_t inner = 0; inner < loop_nesting_graph.size(); ++inner)
    {
      if(inner == outer)
        continue;

      if(outer_instructions.contains(loop_nesting_graph[inner].head))
      {
        loop_nesting_graph.add_edge(inner, outer);
      }
    }
  }

  auto topsorted_size = loop_nesting_graph.topsort().size();
  INVARIANT(
    topsorted_size == loop_nesting_graph.size(),
    "loop_nesting_graph must be acyclic");

  return loop_nesting_graph;
}
