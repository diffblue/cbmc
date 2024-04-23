/*******************************************************************\

Module: Utility functions for Kani code contracts.

Author: Qinheping Hu, qinhh@amazon.com

\*******************************************************************/

#include "utils_kani.h"

#include <analyses/natural_loops.h>

bool is_kani_loop_invariant(const goto_programt::instructiont instr)
{
  if(!instr.is_function_call())
    return false;

  auto s = id2string(to_symbol_expr(instr.call_function()).get_identifier());
  return (s.find("kani_loop_invariant") != std::string::npos) &&
         (s.find("kani_loop_invariant_") == std::string::npos);
}

bool is_kani_loop_invariant_begin(const goto_programt::instructiont instr)
{
  if(!instr.is_function_call())
    return false;

  auto s = id2string(to_symbol_expr(instr.call_function()).get_identifier());
  return s.find("kani_loop_invariant_begin") != std::string::npos;
}

bool is_kani_loop_invariant_end(const goto_programt::instructiont instr)
{
  if(!instr.is_function_call())
    return false;

  auto s = id2string(to_symbol_expr(instr.call_function()).get_identifier());
  return s.find("kani_loop_invariant_end") != std::string::npos;
}

void annotate_kani_loop_invariants(goto_programt &body, messaget &log)
{
  // The place holder function call
  //   kani_loop_invariant(cond)
  // indicate its successor loop latch contains loop invariants.
  // So for each such function call, we find the loop end for it and
  // annotate loop contracts to the loop end.
  // Note that here we only annotate 'true' to indicate it contains
  // loop contracts. And will later get the loop contracts with another pass.

  natural_loops_mutablet natural_loops(body);
  std::set<goto_programt::targett, goto_programt::target_less_than>
    loop_latches;

  // Collect all latches
  for(const auto &loop_head_and_content : natural_loops.loop_map)
  {
    const auto &loop_content = loop_head_and_content.second;
    // Skip empty loops and self-looped node.
    if(loop_content.size() <= 1)
      continue;

    auto loop_head = loop_head_and_content.first;
    auto loop_end = loop_head;

    // Find the last back edge to `loop_head`
    for(const auto &t : loop_content)
    {
      if(
        t->is_goto() && t->get_target() == loop_head &&
        t->location_number > loop_end->location_number)
        loop_end = t;
    }

    if(loop_end == loop_head)
    {
      log.error() << "Could not find end of the loop starting at: "
                  << loop_head->source_location() << messaget::eom;
      throw 0;
    }
    loop_latches.insert(loop_end);
  }

  // Go through all instructions in the body to find the placeholder
  //    kani_loop_invariant()
  for(auto it = body.instructions.begin(); it != body.instructions.end(); it++)
  {
    if(is_kani_loop_invariant(*it))
    {
      auto temp_it = it;
      while(!loop_latches.count(temp_it))
      {
        temp_it = body.get_successors(temp_it).front();
      }

      auto op = and_exprt(true_exprt(), true_exprt());

      temp_it->condition_nonconst().add(ID_C_spec_loop_invariant).swap(op);
    }
  }
}

void get_kani_invariants(
  const goto_functiont &goto_function,
  const goto_programt::const_targett &loop_head,
  exprt::operandst &invariant_clauses,
  goto_programt::instructionst &eval_instructions)
{
  // The loop invariants in kani goto are passed as the instructions
  // right before the loop head, and between two placeholder function
  // calls kani_loop_invariant_begin() and kani_loop_invariant_end().
  auto &body = goto_function.body;

  for(auto it = body.instructions.begin(); it != body.instructions.end(); it++)
  {
    // first find the loop head
    if(it == loop_head)
    {
      // skip irrelevant instructions until we see the placeholder
      while(!is_kani_loop_invariant_end(*it))
      {
        it--;
      }
      // skip the placeholder
      it--;

      // copy and store all instructions between the two placeholders
      while(!is_kani_loop_invariant_begin(*it))
      {
        // except for goto and dead
        // because here the goto is not a real goto, but just goto the next
        // instruction.
        // Dead instructions are for those temporary variables and can be
        // safely ignored here.
        if(!it->is_goto() && !it->is_dead())
        {
          auto new_instruction = goto_programt::instructiont(*it);
          new_instruction.target_number =
            goto_programt::instructiont::nil_target;
          eval_instructions.push_front(new_instruction);
        }

        // The only function call assign the evaluated result to a boolean
        // variable. We will use the result variable as loop invariants.
        if(it->is_function_call())
        {
          invariant_clauses.push_back(
            typecast_exprt(it->call_lhs(), bool_typet()));
        }
        it--;
      }
      return;
    }
  }
  UNREACHABLE;
}
