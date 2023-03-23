/*******************************************************************\

Module: Dynamic frame condition checking for loop contracts

Author: Qinheping Hu, qinhh@amazon.com
Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

#include "dfcc_check_loop_normal_form.h"

#include <analyses/natural_loops.h>
#include <goto-instrument/contracts/utils.h>

void dfcc_check_loop_normal_form(goto_programt &goto_program, messaget &log)
{
  natural_loops_mutablet natural_loops(goto_program);

  // instruction span for each loop
  std::vector<std::pair<goto_programt::targett, goto_programt::targett>> spans;

  for(auto &loop : natural_loops.loop_map)
  {
    auto head = loop.first;
    auto &loop_instructions = loop.second;

    if(loop_instructions.size() <= 1)
    {
      // Ignore single instruction loops of the form
      // `LOOP: IF cond GOTO LOOP;`
      continue;
    }

    auto latch = head;
    bool latch_found = false;

    // Find latch and check it is unique
    for(const auto &t : loop_instructions)
    {
      if(t->is_goto() && t->get_target() == head)
      {
        if(latch_found)
        {
          log.error() << "Loop starting at:"
                      << "\n- head: " << head->source_location()
                      << "\nhas more than one latch instruction:"
                      << "\n- latch1: " << latch->source_location()
                      << "\n- latch2: " << t->source_location()
                      << messaget::eom;
          throw analysis_exceptiont(
            "Found loop with more than one latch instruction");
        }
        latch = t;
        latch_found = true;
      }
    }

    INVARIANT(latch_found, "Natural loop latch found");

    // Check that instruction spans are not overlapping
    for(const auto &span : spans)
    {
      bool head_in_span =
        span.first->location_number <= head->location_number &&
        head->location_number <= span.second->location_number;

      bool latch_in_span =
        span.first->location_number <= latch->location_number &&
        latch->location_number <= span.second->location_number;

      if(head_in_span != latch_in_span)
      {
        log.error() << "Loop spanning:"
                    << "\n- head: " << head->source_location()
                    << "\n- latch: " << latch->source_location()
                    << "\noverlaps loop spanning:"
                    << "\n- head: " << span.first->source_location()
                    << "\n- latch: " << span.second->source_location()
                    << messaget::eom;
        throw analysis_exceptiont(
          "Found loops with overlapping instruction spans");
      }
    }

    spans.push_back({head, latch});

    // Check that:
    // 1. all loop instructions are in the range [head, latch]
    // 2. except for the head instruction, no incoming edge from outside the
    // loop
    for(const auto &i : loop_instructions)
    {
      if(
        i->location_number < head->location_number ||
        i->location_number > latch->location_number)
      {
        log.error() << "Loop body instruction at:"
                    << "\n- " << i->source_location() << "\nis outside of"
                    << "\n- head: " << head->source_location()
                    << "\n- latch: " << latch->source_location()
                    << messaget::eom;
        throw analysis_exceptiont(
          "Found loop body instruction outside of the [head, latch] "
          "instruction span");
      }

      for(const auto &from : i->incoming_edges)
      {
        if(i != head && !loop_instructions.contains(from))
        {
          log.error() << "Loop body instruction at:"
                      << "\n- " << i->source_location()
                      << "\n has incoming edge from outside the loop at:"
                      << "\n- " << from->source_location() << messaget::eom;

          throw analysis_exceptiont(
            "Found loop body instruction with incoming edge from outside the "
            "loop");
        }
      }
    }

    // Check if a loop contains another loop's head (resp. latch) then
    // it also contains the latch (resp. head)
    for(auto &other_loop : natural_loops.loop_map)
    {
      auto &other_loop_instructions = other_loop.second;
      bool contains_head = other_loop_instructions.contains(head);
      bool contains_latch = other_loop_instructions.contains(latch);
      INVARIANT(
        contains_head == contains_latch,
        "nested loop head and latch are in outer loop");
    }

    // all checks passed, now we perform some instruction rewriting

    // Convert conditional latch into exiting + unconditional latch.
    // ```
    //       IF g THEN GOTO HEAD
    // --------------------------
    //       IF !g THEN GOTO EXIT
    //       GOTO HEAD
    // EXIT: SKIP
    // ```
    if(latch->has_condition() && !latch->condition().is_true())
    {
      const source_locationt &loc = latch->source_location();
      const auto &exit =
        goto_program.insert_after(latch, goto_programt::make_skip(loc));

      insert_before_and_update_jumps(
        goto_program,
        latch,
        goto_programt::make_goto(
          exit, not_exprt(latch->condition()), latch->source_location()));

      // CAUTION: The condition expression needs to be updated in place because
      // this is where loop contract clauses are stored as extra ireps.
      // Overwriting this expression with a fresh expression will also lose the
      // loop contract.
      exprt latch_condition = latch->condition();
      latch_condition.set(ID_value, ID_true);
      *latch = goto_programt::make_goto(head, latch_condition, loc);
    }

    // The latch node is now an unconditional jump.

    // insert a SKIP pre-head node and reroute all incoming edges to that node,
    // except for edge coming from the latch.
    insert_before_and_update_jumps(
      goto_program, head, goto_programt::make_skip(head->source_location()));
    latch->set_target(head);
  }
  goto_program.update();
}
