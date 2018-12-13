/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <algorithm>

#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>

#include <analyses/dirty.h>
#include <util/simplify_expr.h>

void goto_symext::symex_goto(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;
  statet::framet &frame=state.top();

  if(state.guard.is_false())
  {
    // next instruction
    symex_transition(state);
    return; // nothing to do
  }

  exprt old_guard=instruction.guard;
  clean_expr(old_guard, state, false);

  exprt new_guard=old_guard;
  state.rename(new_guard, ns);
  do_simplify(new_guard);

  if(new_guard.is_false())
  {
    target.location(state.guard.as_expr(), state.source);

    // next instruction
    symex_transition(state);
    return; // nothing to do
  }

  target.goto_instruction(state.guard.as_expr(), new_guard, state.source);

  DATA_INVARIANT(
    !instruction.targets.empty(), "goto should have at least one target");

  // we only do deterministic gotos for now
  DATA_INVARIANT(
    instruction.targets.size() == 1, "no support for non-deterministic gotos");

  goto_programt::const_targett goto_target=
    instruction.get_target();

  const bool backward = instruction.is_backwards_goto();

  if(backward)
  {
    // is it label: goto label; or while(cond); - popular in SV-COMP
    if(
      symex_config.self_loops_to_assumptions &&
      (goto_target == state.source.pc ||
       (instruction.incoming_edges.size() == 1 &&
        *instruction.incoming_edges.begin() == goto_target)))
    {
      // generate assume(false) or a suitable negation if this
      // instruction is a conditional goto
      if(new_guard.is_true())
        symex_assume(state, false_exprt());
      else
        symex_assume(state, not_exprt(new_guard));

      // next instruction
      symex_transition(state);
      return;
    }

    unsigned &unwind=
      frame.loop_iterations[goto_programt::loop_id(*state.source.pc)].count;
    unwind++;

    if(should_stop_unwind(state.source, state.call_stack(), unwind))
    {
      loop_bound_exceeded(state, new_guard);

      // next instruction
      symex_transition(state);
      return;
    }

    if(new_guard.is_true())
    {
      symex_transition(state, goto_target, true);
      return; // nothing else to do
    }
  }

  exprt simpl_state_guard = state.guard.as_expr();
  do_simplify(simpl_state_guard);

  // No point executing both branches of an unconditional goto.
  if(
    new_guard.is_true() && // We have an unconditional goto, AND
    // either there are no blocks between us and the target in the
    // surrounding scope
    (simpl_state_guard.is_true() ||
     // or there is another block, but we're doing path exploration so
     // we're going to skip over it for now and return to it later.
     symex_config.doing_path_exploration))
  {
    DATA_INVARIANT(
      instruction.targets.size() > 0,
      "Instruction is an unconditional goto with no target: " +
        instruction.code.pretty());
    symex_transition(state, instruction.get_target(), true);
    return;
  }

  goto_programt::const_targett new_state_pc, state_pc;
  symex_targett::sourcet original_source=state.source;

  if(!backward)
  {
    new_state_pc=goto_target;
    state_pc=state.source.pc;
    state_pc++;

    // skip dead instructions
    if(new_guard.is_true())
      while(state_pc!=goto_target && !state_pc->is_target())
        ++state_pc;

    if(state_pc==goto_target)
    {
      symex_transition(state, goto_target, false);
      return; // nothing else to do
    }
  }
  else
  {
    new_state_pc=state.source.pc;
    new_state_pc++;
    state_pc=goto_target;
  }

  // Normally the next instruction to execute would be state_pc and we save
  // new_state_pc for later. But if we're executing from a saved state, then
  // new_state_pc should be the state that we saved from earlier, so let's
  // execute that instead.
  if(state.has_saved_jump_target)
  {
    INVARIANT(
      new_state_pc == state.saved_target,
      "Tried to explore the other path of a branch, but the next "
      "instruction along that path is not the same as the instruction "
      "that we saved at the branch point. Saved instruction is " +
        state.saved_target->code.pretty() +
        "\nwe were intending "
        "to explore " +
        new_state_pc->code.pretty() +
        "\nthe "
        "instruction we think we saw on a previous path exploration is " +
        state_pc->code.pretty());
    goto_programt::const_targett tmp = new_state_pc;
    new_state_pc = state_pc;
    state_pc = tmp;

    log.debug() << "Resuming from jump target '" << state_pc->source_location
                << "'" << log.eom;
  }
  else if(state.has_saved_next_instruction)
  {
    log.debug() << "Resuming from next instruction '"
                << state_pc->source_location << "'" << log.eom;
  }
  else if(symex_config.doing_path_exploration)
  {
    // We should save both the instruction after this goto, and the target of
    // the goto.

    path_storaget::patht next_instruction(target, state);
    next_instruction.state.saved_target = state_pc;
    next_instruction.state.has_saved_next_instruction = true;

    path_storaget::patht jump_target(target, state);
    jump_target.state.saved_target = new_state_pc;
    jump_target.state.has_saved_jump_target = true;
    // `forward` tells us where the branch we're _currently_ executing is
    // pointing to; this needs to be inverted for the branch that we're saving,
    // so let its truth value for `backwards` be the same as ours for `forward`.

    log.debug() << "Saving next instruction '"
                << next_instruction.state.saved_target->source_location << "'"
                << log.eom;
    log.debug() << "Saving jump target '"
                << jump_target.state.saved_target->source_location << "'"
                << log.eom;
    path_storage.push(next_instruction, jump_target);

    // It is now up to the caller of symex to decide which path to continue
    // executing. Signal to the caller that states have been pushed (therefore
    // symex has not yet completed and must be resumed), and bail out.
    should_pause_symex = true;
    return;
  }

  // put into state-queue
  statet::goto_state_listt &goto_state_list=
    state.top().goto_state_map[new_state_pc];

  goto_state_list.push_back(statet::goto_statet(state));

  symex_transition(state, state_pc, backward);

  // adjust guards
  if(new_guard.is_true())
  {
    state.guard = false_exprt();
  }
  else
  {
    // produce new guard symbol
    exprt guard_expr;

    if(
      new_guard.id() == ID_symbol ||
      (new_guard.id() == ID_not &&
       to_not_expr(new_guard).op().id() == ID_symbol))
    {
      guard_expr=new_guard;
    }
    else
    {
      symbol_exprt guard_symbol_expr=
        symbol_exprt(guard_identifier, bool_typet());
      exprt new_rhs = boolean_negate(new_guard);

      ssa_exprt new_lhs(guard_symbol_expr);
      state.rename(new_lhs, ns, goto_symex_statet::L1);
      state.assignment(new_lhs, new_rhs, ns, true, false);

      guardt guard;

      log.conditional_output(
        log.debug(),
        [this, &new_lhs](messaget::mstreamt &mstream) {
          mstream << "Assignment to " << new_lhs.get_identifier()
                  << " [" << pointer_offset_bits(new_lhs.type(), ns).value_or(0) << " bits]"
                  << messaget::eom;
        });

      target.assignment(
        guard.as_expr(),
        new_lhs, new_lhs, guard_symbol_expr,
        new_rhs,
        original_source,
        symex_targett::assignment_typet::GUARD);

      guard_expr = boolean_negate(guard_symbol_expr);
      state.rename(guard_expr, ns);
    }

    if(state.has_saved_jump_target)
    {
      if(!backward)
        state.guard.add(guard_expr);
      else
        state.guard.add(boolean_negate(guard_expr));
    }
    else
    {
      statet::goto_statet &new_state = goto_state_list.back();
      if(!backward)
      {
        new_state.guard.add(guard_expr);
        state.guard.add(boolean_negate(guard_expr));
      }
      else
      {
        state.guard.add(guard_expr);
        new_state.guard.add(boolean_negate(guard_expr));
      }
    }
  }
}

void goto_symext::merge_gotos(statet &state)
{
  statet::framet &frame=state.top();

  // first, see if this is a target at all
  statet::goto_state_mapt::iterator state_map_it=
    frame.goto_state_map.find(state.source.pc);

  if(state_map_it==frame.goto_state_map.end())
    return; // nothing to do

  // we need to merge
  statet::goto_state_listt &state_list=state_map_it->second;

  for(statet::goto_state_listt::reverse_iterator
      list_it=state_list.rbegin();
      list_it!=state_list.rend();
      list_it++)
    merge_goto(*list_it, state);

  // clean up to save some memory
  frame.goto_state_map.erase(state_map_it);
}

void goto_symext::merge_goto(
  const statet::goto_statet &goto_state,
  statet &state)
{
  // check atomic section
  if(state.atomic_section_id != goto_state.atomic_section_id)
    throw incorrect_goto_program_exceptiont(
      "atomic sections differ across branches",
      state.source.pc->source_location);

  // do SSA phi functions
  phi_function(goto_state, state);

  merge_value_sets(goto_state, state);

  // adjust guard
  state.guard|=goto_state.guard;

  // adjust depth
  state.depth=std::min(state.depth, goto_state.depth);
}

void goto_symext::merge_value_sets(
  const statet::goto_statet &src,
  statet &dest)
{
  if(dest.guard.is_false())
  {
    dest.value_set=src.value_set;
    return;
  }

  dest.value_set.make_union(src.value_set);
}

/// Applies f to `(k, ssa, i, j)` if the first map maps k to (ssa, i) and
/// the second to (ssa', j). If the first map has an entry for k but not the
/// second one then j is 0, and when the first map has no entry for k then i = 0
static void for_each2(
  const std::map<irep_idt, std::pair<ssa_exprt, unsigned>> &first_map,
  const std::map<irep_idt, std::pair<ssa_exprt, unsigned>> &second_map,
  const std::function<void(const ssa_exprt &, unsigned, unsigned)> &f)
{
  auto second_it = second_map.begin();
  for(const auto &first_pair : first_map)
  {
    while(second_it != second_map.end() && second_it->first < first_pair.first)
    {
      f(second_it->second.first, 0, second_it->second.second);
      ++second_it;
    }
    const ssa_exprt &ssa = first_pair.second.first;
    const unsigned count = first_pair.second.second;
    if(second_it != second_map.end() && second_it->first == first_pair.first)
    {
      f(ssa, count, second_it->second.second);
      ++second_it;
    }
    else
      f(ssa, count, 0);
  }
  while(second_it != second_map.end())
  {
    f(second_it->second.first, 0, second_it->second.second);
    ++second_it;
  }
}

/// Helper function for \c phi_function which merges the names of an identifier
/// for two different states.
/// \param goto_state: first state
/// \param[in, out] dest_state: second state
/// \param ns: namespace
/// \param diff_guard: difference between the guards of the two states
/// \param guard_identifier: prefix used for goto symex guards
/// \param[out] log: logger for debug messages
/// \param do_simplify: should the right-hand-side of the assignment that is
///   added to the target be simplified
/// \param[out] target: equation that will receive the resulting assignment
/// \param ssa: SSA expression to merge
/// \param goto_count: current level 2 count in \p goto_state of
///   \p l1_identifier
/// \param dest_count: level 2 count in \p dest_state of \p l1_identifier
static void merge_names(
  const goto_symext::statet::goto_statet &goto_state,
  goto_symext::statet &dest_state,
  const namespacet &ns,
  const guardt &diff_guard,
  const irep_idt &guard_identifier,
  messaget &log,
  const bool do_simplify,
  symex_target_equationt &target,
  const ssa_exprt &ssa,
  const unsigned goto_count,
  const unsigned dest_count)
{
  const irep_idt l1_identifier = ssa.get_identifier();
  const irep_idt &obj_identifier = ssa.get_object_name();

  if(obj_identifier == guard_identifier)
    return; // just a guard, don't bother

  if(goto_count == dest_count)
    return; // not at all changed

  // changed!

  // shared variables are renamed on every access anyway, we don't need to
  // merge anything
  const symbolt &symbol = ns.lookup(obj_identifier);

  // shared?
  if(
    dest_state.atomic_section_id == 0 && dest_state.threads.size() >= 2 &&
    (symbol.is_shared() || (dest_state.dirty)(symbol.name)))
    return; // no phi nodes for shared stuff

  // don't merge (thread-)locals across different threads, which
  // may have been introduced by symex_start_thread (and will
  // only later be removed from level2.current_names by pop_frame
  // once the thread is executed)
  const irep_idt level_0 = ssa.get_level_0();
  if(!level_0.empty() && level_0 != std::to_string(dest_state.source.thread_nr))
    return;

  exprt goto_state_rhs = ssa, dest_state_rhs = ssa;

  {
    const auto p_it = goto_state.propagation.find(l1_identifier);

    if(p_it != goto_state.propagation.end())
      goto_state_rhs = p_it->second;
    else
      to_ssa_expr(goto_state_rhs).set_level_2(goto_count);
  }

  {
    const auto p_it = dest_state.propagation.find(l1_identifier);

    if(p_it != dest_state.propagation.end())
      dest_state_rhs = p_it->second;
    else
      to_ssa_expr(dest_state_rhs).set_level_2(dest_count);
  }

  exprt rhs;

  // Don't add a conditional to the assignment when:
  //  1. Either guard is false, so we can't follow that branch.
  //  2. Either identifier is of generation zero, and so hasn't been
  //     initialized and therefore an invalid target.
  if(dest_state.guard.is_false())
    rhs = goto_state_rhs;
  else if(goto_state.guard.is_false())
    rhs = dest_state_rhs;
  else if(goto_count == 0)
  {
    rhs = dest_state_rhs;
  }
  else if(dest_count == 0)
  {
    rhs = goto_state_rhs;
  }
  else
  {
    rhs = if_exprt(diff_guard.as_expr(), goto_state_rhs, dest_state_rhs);
    if(do_simplify)
      simplify(rhs, ns);
  }

  ssa_exprt new_lhs = ssa;
  const bool record_events = dest_state.record_events;
  dest_state.record_events = false;
  dest_state.assignment(new_lhs, rhs, ns, true, true);
  dest_state.record_events = record_events;

  log.conditional_output(
    log.debug(), [ns, &new_lhs](messaget::mstreamt &mstream) {
      mstream << "Assignment to " << new_lhs.get_identifier() << " ["
              << pointer_offset_bits(new_lhs.type(), ns).value_or(0) << " bits]"
              << messaget::eom;
    });

  target.assignment(
    true_exprt(),
    new_lhs,
    new_lhs,
    new_lhs.get_original_expr(),
    rhs,
    dest_state.source,
    symex_targett::assignment_typet::PHI);
}

void goto_symext::phi_function(
  const statet::goto_statet &goto_state,
  statet &dest_state)
{
  if(
    goto_state.level2_current_names.empty() &&
    dest_state.level2.current_names.empty())
    return;

  guardt diff_guard = goto_state.guard;
  // this gets the diff between the guards
  diff_guard -= dest_state.guard;

  for_each2(
    goto_state.level2_current_names,
    dest_state.level2.current_names,
    [&](const ssa_exprt &ssa, unsigned goto_count, unsigned dest_count) {
      merge_names(
        goto_state,
        dest_state,
        ns,
        diff_guard,
        guard_identifier,
        log,
        symex_config.simplify_opt,
        target,
        ssa,
        goto_count,
        dest_count);
    });
}

void goto_symext::loop_bound_exceeded(
  statet &state,
  const exprt &guard)
{
  const unsigned loop_number=state.source.pc->loop_number;

  exprt negated_cond;

  if(guard.is_true())
    negated_cond=false_exprt();
  else
    negated_cond=not_exprt(guard);

  if(!symex_config.partial_loops)
  {
    if(symex_config.unwinding_assertions)
    {
      // Generate VCC for unwinding assertion.
      vcc(negated_cond,
          "unwinding assertion loop "+std::to_string(loop_number),
          state);

      // add to state guard to prevent further assignments
      state.guard.add(negated_cond);
    }
    else
    {
      // generate unwinding assumption, unless we permit partial loops
      symex_assume(state, negated_cond);
    }
  }
}

bool goto_symext::should_stop_unwind(
  const symex_targett::sourcet &,
  const goto_symex_statet::call_stackt &,
  unsigned)
{
  // by default, we keep going
  return false;
}
