/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <algorithm>

#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/pointer_offset_size.h>
#include <util/std_expr.h>

#include <analyses/dirty.h>

void goto_symext::symex_goto(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;
  statet::framet &frame=state.top();

  exprt old_guard=instruction.guard;
  clean_expr(old_guard, state, false);

  exprt new_guard=old_guard;
  state.rename(new_guard, ns);
  do_simplify(new_guard);

  if(new_guard.is_false() ||
     state.guard.is_false())
  {
    if(!state.guard.is_false())
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

  bool forward=!instruction.is_backwards_goto();

  if(!forward) // backwards?
  {
    // is it label: goto label; or while(cond); - popular in SV-COMP
    if(
      self_loops_to_assumptions &&
      (goto_target == state.source.pc ||
       (instruction.incoming_edges.size() == 1 &&
        *instruction.incoming_edges.begin() == goto_target)))
    {
      // generate assume(false) or a suitable negation if this
      // instruction is a conditional goto
      exprt negated_cond;

      if(new_guard.is_true())
        negated_cond=false_exprt();
      else
        negated_cond=not_exprt(new_guard);

      symex_assume(state, negated_cond);

      // next instruction
      symex_transition(state);
      return;
    }

    unsigned &unwind=
      frame.loop_iterations[goto_programt::loop_id(*state.source.pc)].count;
    unwind++;

    // continue unwinding?
    if(get_unwind(state.source, state.call_stack(), unwind))
    {
      // no!
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
     doing_path_exploration))
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

  if(forward)
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
      symex_transition(state, goto_target);
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
  else if(doing_path_exploration)
  {
    // We should save both the instruction after this goto, and the target of
    // the goto.

    path_storaget::patht next_instruction(target, state);
    next_instruction.state.saved_target = state_pc;
    next_instruction.state.has_saved_next_instruction = true;
    next_instruction.state.saved_target_is_backwards = !forward;

    path_storaget::patht jump_target(target, state);
    jump_target.state.saved_target = new_state_pc;
    jump_target.state.has_saved_jump_target = true;
    // `forward` tells us where the branch we're _currently_ executing is
    // pointing to; this needs to be inverted for the branch that we're saving,
    // so let its truth value for `backwards` be the same as ours for `forward`.
    jump_target.state.saved_target_is_backwards = forward;

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

  symex_transition(state, state_pc, !forward);

  // adjust guards
  if(new_guard.is_true())
  {
    state.guard.make_false();
  }
  else
  {
    // produce new guard symbol
    exprt guard_expr;

    if(new_guard.id()==ID_symbol ||
       (new_guard.id()==ID_not &&
        new_guard.operands().size()==1 &&
        new_guard.op0().id()==ID_symbol))
      guard_expr=new_guard;
    else
    {
      symbol_exprt guard_symbol_expr=
        symbol_exprt(guard_identifier, bool_typet());
      exprt new_rhs=new_guard;
      new_rhs.make_not();

      ssa_exprt new_lhs(guard_symbol_expr);
      state.rename(new_lhs, ns, goto_symex_statet::L1);
      state.assignment(new_lhs, new_rhs, ns, true, false);

      guardt guard;

      log.conditional_output(
        log.debug(),
        [this, &new_lhs](messaget::mstreamt &mstream) {
          mstream << "Assignment to " << new_lhs.get_identifier()
                  << " [" << pointer_offset_bits(new_lhs.type(), ns) << " bits]"
                  << messaget::eom;
        });

      target.assignment(
        guard.as_expr(),
        new_lhs, new_lhs, guard_symbol_expr,
        new_rhs,
        original_source,
        symex_targett::assignment_typet::GUARD);

      guard_expr=guard_symbol_expr;
      guard_expr.make_not();
      state.rename(guard_expr, ns);
    }

    if(state.has_saved_jump_target)
    {
      if(forward)
        state.guard.add(guard_expr);
      else
      {
        guard_expr.make_not();
        state.guard.add(guard_expr);
      }
    }
    else
    {
      statet::goto_statet &new_state = goto_state_list.back();
      if(forward)
      {
        new_state.guard.add(guard_expr);
        guard_expr.make_not();
        state.guard.add(guard_expr);
      }
      else
      {
        state.guard.add(guard_expr);
        guard_expr.make_not();
        new_state.guard.add(guard_expr);
      }
    }
  }
}

void goto_symext::symex_step_goto(statet &state, bool taken)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  exprt guard(instruction.guard);
  dereference(guard, state, false);
  state.rename(guard, ns);

  if(!taken)
    guard.make_not();

  state.guard.guard_expr(guard);
  do_simplify(guard);

  target.assumption(state.guard.as_expr(), guard, state.source);
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

void goto_symext::phi_function(
  const statet::goto_statet &goto_state,
  statet &dest_state)
{
  // go over all variables to see what changed
  std::unordered_set<ssa_exprt, irep_hash> variables;

  goto_state.level2_get_variables(variables);
  dest_state.level2.get_variables(variables);

  guardt diff_guard;

  if(!variables.empty())
  {
    diff_guard=goto_state.guard;

    // this gets the diff between the guards
    diff_guard-=dest_state.guard;
  }

  for(std::unordered_set<ssa_exprt, irep_hash>::const_iterator
      it=variables.begin();
      it!=variables.end();
      it++)
  {
    const irep_idt l1_identifier=it->get_identifier();
    const irep_idt &obj_identifier=it->get_object_name();

    if(obj_identifier==guard_identifier)
      continue; // just a guard, don't bother

    if(goto_state.level2_current_count(l1_identifier)==
       dest_state.level2.current_count(l1_identifier))
      continue; // not at all changed

    // changed!

    // shared variables are renamed on every access anyway, we don't need to
    // merge anything
    const symbolt &symbol=ns.lookup(obj_identifier);

    // shared?
    if(
      dest_state.atomic_section_id == 0 && dest_state.threads.size() >= 2 &&
      (symbol.is_shared() || (dest_state.dirty)(symbol.name)))
      continue; // no phi nodes for shared stuff

    // don't merge (thread-)locals across different threads, which
    // may have been introduced by symex_start_thread (and will
    // only later be removed from level2.current_names by pop_frame
    // once the thread is executed)
    if(!it->get_level_0().empty() &&
       it->get_level_0()!=std::to_string(dest_state.source.thread_nr))
      continue;

    exprt goto_state_rhs=*it, dest_state_rhs=*it;

    {
      goto_symex_statet::propagationt::valuest::const_iterator p_it=
        goto_state.propagation.values.find(l1_identifier);

      if(p_it!=goto_state.propagation.values.end())
        goto_state_rhs=p_it->second;
      else
        to_ssa_expr(goto_state_rhs).set_level_2(
          goto_state.level2_current_count(l1_identifier));
    }

    {
      goto_symex_statet::propagationt::valuest::const_iterator p_it=
        dest_state.propagation.values.find(l1_identifier);

      if(p_it!=dest_state.propagation.values.end())
        dest_state_rhs=p_it->second;
      else
        to_ssa_expr(dest_state_rhs).set_level_2(
          dest_state.level2.current_count(l1_identifier));
    }

    exprt rhs;

    // Don't add a conditional to the assignment when:
    //  1. Either guard is false, so we can't follow that branch.
    //  2. Either identifier is of generation zero, and so hasn't been
    //     initialized and therefor an invalid target.
    if(dest_state.guard.is_false())
      rhs=goto_state_rhs;
    else if(goto_state.guard.is_false())
      rhs=dest_state_rhs;
    else if(goto_state.level2_current_count(l1_identifier) == 0)
    {
      rhs = dest_state_rhs;
    }
    else if(dest_state.level2.current_count(l1_identifier) == 0)
    {
      rhs = goto_state_rhs;
    }
    else
    {
      rhs=if_exprt(diff_guard.as_expr(), goto_state_rhs, dest_state_rhs);
      do_simplify(rhs);
    }

    ssa_exprt new_lhs=*it;
    const bool record_events=dest_state.record_events;
    dest_state.record_events=false;
    dest_state.assignment(new_lhs, rhs, ns, true, true);
    dest_state.record_events=record_events;

    log.conditional_output(
      log.debug(),
      [this, &new_lhs](messaget::mstreamt &mstream) {
        mstream << "Assignment to " << new_lhs.get_identifier()
                << " [" << pointer_offset_bits(new_lhs.type(), ns) << " bits]"
                << messaget::eom;
      });

    target.assignment(
      true_exprt(),
      new_lhs, new_lhs, new_lhs.get_original_expr(),
      rhs,
      dest_state.source,
      symex_targett::assignment_typet::PHI);
  }
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

  bool unwinding_assertions=
    options.get_bool_option("unwinding-assertions");

  bool partial_loops=
    options.get_bool_option("partial-loops");

  if(!partial_loops)
  {
    if(unwinding_assertions)
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

bool goto_symext::get_unwind(
  const symex_targett::sourcet &,
  const goto_symex_statet::call_stackt &,
  unsigned)
{
  // by default, we keep going
  return false;
}
