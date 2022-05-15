/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <langapi/language_util.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/value_set_dereference.h>

#include "goto_symex.h"
#include "goto_symex_is_constant.h"
#include "path_storage.h"

#include <algorithm>

void goto_symext::apply_goto_condition(
  goto_symex_statet &current_state,
  goto_statet &jump_taken_state,
  goto_statet &jump_not_taken_state,
  const exprt &original_guard,
  const exprt &new_guard,
  const namespacet &ns)
{
  // It would be better to call try_filter_value_sets after apply_condition,
  // and pass nullptr for value sets which apply_condition successfully updated
  // already. However, try_filter_value_sets calls rename to do constant
  // propagation, and apply_condition can update the constant propagator. Since
  // apply condition will never succeed on both jump_taken_state and
  // jump_not_taken_state, it should be possible to pass a reference to an
  // unmodified goto_statet to use for renaming. But renaming needs a
  // goto_symex_statet, not just a goto_statet, and we only have access to one
  // of those. A future improvement would be to split rename into two parts:
  // one part on goto_symex_statet which is non-const and deals with
  // l2 thread reads, and one part on goto_statet which is const and could be
  // used in try_filter_value_sets.

  try_filter_value_sets(
    current_state,
    original_guard,
    jump_taken_state.value_set,
    &jump_taken_state.value_set,
    &jump_not_taken_state.value_set,
    ns);

  if(!symex_config.constant_propagation)
    return;

  jump_taken_state.apply_condition(new_guard, current_state, ns);

  // Could use not_exprt + simplify, but let's avoid paying that cost on quite
  // a hot path:
  const exprt negated_new_guard = boolean_negate(new_guard);
  jump_not_taken_state.apply_condition(negated_new_guard, current_state, ns);
}

/// Try to evaluate a simple pointer comparison.
/// \param operation: ID_equal or ID_not_equal
/// \param symbol_expr: The symbol expression in the condition
/// \param other_operand: The other expression in the condition; we only support
///   an address of expression, a typecast of an address of expression or a
///   null pointer, and return an empty optionalt in all other cases
/// \param value_set: The value-set for looking up what the symbol can point to
/// \param language_mode: The language mode
/// \param ns: A namespace
/// \return If we were able to evaluate the condition as true or false then we
///   return that, otherwise we return an empty optionalt
static optionalt<renamedt<exprt, L2>> try_evaluate_pointer_comparison(
  const irep_idt &operation,
  const symbol_exprt &symbol_expr,
  const exprt &other_operand,
  const value_sett &value_set,
  const irep_idt language_mode,
  const namespacet &ns)
{
  const constant_exprt *constant_expr =
    expr_try_dynamic_cast<constant_exprt>(other_operand);

  if(
    skip_typecast(other_operand).id() != ID_address_of &&
    (!constant_expr || !is_null_pointer(*constant_expr)))
  {
    return {};
  }

  const ssa_exprt *ssa_symbol_expr =
    expr_try_dynamic_cast<ssa_exprt>(symbol_expr);

  ssa_exprt l1_expr{*ssa_symbol_expr};
  l1_expr.remove_level_2();
  const std::vector<exprt> value_set_elements =
    value_set.get_value_set(l1_expr, ns);

  bool constant_found = false;

  for(const auto &value_set_element : value_set_elements)
  {
    if(
      value_set_element.id() == ID_unknown ||
      value_set_element.id() == ID_invalid ||
      is_failed_symbol(
        to_object_descriptor_expr(value_set_element).root_object()) ||
      to_object_descriptor_expr(value_set_element).offset().id() == ID_unknown)
    {
      // We can't conclude anything about the value-set
      return {};
    }

    if(!constant_found)
    {
      if(value_set_dereferencet::should_ignore_value(
           value_set_element, false, language_mode))
      {
        continue;
      }

      value_set_dereferencet::valuet value =
        value_set_dereferencet::build_reference_to(
          value_set_element, symbol_expr, ns);

      // use the simplifier to test equality as we need to skip over typecasts
      // and cannot rely on canonical representations, which would permit a
      // simple syntactic equality test
      exprt test_equal = simplify_expr(
        equal_exprt{
          typecast_exprt::conditional_cast(value.pointer, other_operand.type()),
          other_operand},
        ns);
      if(test_equal.is_true())
      {
        constant_found = true;
        // We can't break because we have to make sure we find any instances of
        // ID_unknown or ID_invalid
      }
      else if(!test_equal.is_false())
      {
        // We can't conclude anything about the value-set
        return {};
      }
    }
  }

  if(!constant_found)
  {
    // The symbol cannot possibly have the value \p other_operand because it
    // isn't in the symbol's value-set
    return operation == ID_equal ? make_renamed<L2>(false_exprt{})
                                 : make_renamed<L2>(true_exprt{});
  }
  else if(value_set_elements.size() == 1)
  {
    // The symbol must have the value \p other_operand because it is the only
    // thing in the symbol's value-set
    return operation == ID_equal ? make_renamed<L2>(true_exprt{})
                                 : make_renamed<L2>(false_exprt{});
  }
  else
  {
    return {};
  }
}

/// Check if we have a simple pointer comparison, and if so try to evaluate it.
/// \param renamed_expr: The L2-renamed expression to check
/// \param value_set: The value-set for looking up what the symbol can point to
/// \param language_mode: The language mode
/// \param ns: A namespace
/// \return If we were able to evaluate the condition as true or false then we
///   return that, otherwise we return an empty optionalt
static optionalt<renamedt<exprt, L2>> try_evaluate_pointer_comparison(
  const renamedt<exprt, L2> &renamed_expr,
  const value_sett &value_set,
  const irep_idt &language_mode,
  const namespacet &ns)
{
  const exprt &expr = renamed_expr.get();

  if(expr.id() != ID_equal && expr.id() != ID_notequal)
    return {};

  if(!can_cast_type<pointer_typet>(to_binary_expr(expr).op0().type()))
    return {};

  exprt lhs = to_binary_expr(expr).op0(), rhs = to_binary_expr(expr).op1();
  if(can_cast_expr<symbol_exprt>(rhs))
    std::swap(lhs, rhs);

  const symbol_exprt *symbol_expr_lhs =
    expr_try_dynamic_cast<symbol_exprt>(lhs);

  if(!symbol_expr_lhs)
    return {};

  if(!goto_symex_is_constantt()(rhs))
    return {};

  return try_evaluate_pointer_comparison(
    expr.id(), *symbol_expr_lhs, rhs, value_set, language_mode, ns);
}

renamedt<exprt, L2> try_evaluate_pointer_comparisons(
  renamedt<exprt, L2> condition,
  const value_sett &value_set,
  const irep_idt &language_mode,
  const namespacet &ns)
{
  selectively_mutate(
    condition,
    [&value_set, &language_mode, &ns](const renamedt<exprt, L2> &expr) {
      return try_evaluate_pointer_comparison(
        expr, value_set, language_mode, ns);
    });

  return condition;
}

void goto_symext::symex_goto(statet &state)
{
  PRECONDITION(state.reachable);

  const goto_programt::instructiont &instruction=*state.source.pc;

  exprt new_guard = clean_expr(instruction.condition(), state, false);

  renamedt<exprt, L2> renamed_guard = state.rename(std::move(new_guard), ns);
  renamed_guard = try_evaluate_pointer_comparisons(
    std::move(renamed_guard), state.value_set, language_mode, ns);
  if(symex_config.simplify_opt)
    renamed_guard.simplify(ns);
  new_guard = renamed_guard.get();

  if(new_guard.is_false())
  {
    target.location(state.guard.as_expr(), state.source);

    // next instruction
    symex_transition(state);
    return; // nothing to do
  }

  target.goto_instruction(state.guard.as_expr(), renamed_guard, state.source);

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
      // label: goto label; or do {} while(cond);
      (goto_target == state.source.pc ||
       // while(cond);
       (instruction.incoming_edges.size() == 1 &&
        *instruction.incoming_edges.begin() == goto_target &&
        goto_target->is_goto() && new_guard.is_true())))
    {
      // generate assume(false) or a suitable negation if this
      // instruction is a conditional goto
      exprt negated_guard = not_exprt{new_guard};
      do_simplify(negated_guard);
      log.statistics() << "replacing self-loop at "
                       << state.source.pc->source_location() << " by assume("
                       << from_expr(ns, state.source.function_id, negated_guard)
                       << ")" << messaget::eom;
      if(symex_config.unwinding_assertions)
      {
        log.warning()
          << "no unwinding assertion will be generated for self-loop at "
          << state.source.pc->source_location() << messaget::eom;
      }
      symex_assume_l2(state, negated_guard);

      // next instruction
      symex_transition(state);
      return;
    }

    const auto loop_id =
      goto_programt::loop_id(state.source.function_id, *state.source.pc);

    unsigned &unwind = state.call_stack().top().loop_iterations[loop_id].count;
    unwind++;

    if(should_stop_unwind(state.source, state.call_stack(), unwind))
    {
      // we break the loop
      loop_bound_exceeded(state, new_guard);

      // next instruction
      symex_transition(state);
      return;
    }

    if(new_guard.is_true())
    {
      // we continue executing the loop
      if(check_break(loop_id, unwind))
      {
        should_pause_symex = true;
      }
      symex_transition(state, goto_target, true);
      return; // nothing else to do
    }
  }

  // No point executing both branches of an unconditional goto.
  if(
    new_guard.is_true() && // We have an unconditional goto, AND
    // either there are no reachable blocks between us and the target in the
    // surrounding scope (because state.guard == true implies there is no path
    // around this GOTO instruction)
    (state.guard.is_true() ||
     // or there is another block, but we're doing path exploration so
     // we're going to skip over it for now and return to it later.
     symex_config.doing_path_exploration))
  {
    DATA_INVARIANT(
      instruction.targets.size() > 0,
      "Instruction is an unconditional goto with no target: " +
        instruction.code().pretty());
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
        state.saved_target->code().pretty() +
        "\nwe were intending "
        "to explore " +
        new_state_pc->code().pretty() +
        "\nthe "
        "instruction we think we saw on a previous path exploration is " +
        state_pc->code().pretty());
    goto_programt::const_targett tmp = new_state_pc;
    new_state_pc = state_pc;
    state_pc = tmp;

    log.debug() << "Resuming from jump target '" << state_pc->source_location()
                << "'" << log.eom;
  }
  else if(state.has_saved_next_instruction)
  {
    log.debug() << "Resuming from next instruction '"
                << state_pc->source_location() << "'" << log.eom;
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
                << next_instruction.state.saved_target->source_location() << "'"
                << log.eom;
    log.debug() << "Saving jump target '"
                << jump_target.state.saved_target->source_location() << "'"
                << log.eom;
    path_storage.push(next_instruction);
    path_storage.push(jump_target);

    // It is now up to the caller of symex to decide which path to continue
    // executing. Signal to the caller that states have been pushed (therefore
    // symex has not yet completed and must be resumed), and bail out.
    should_pause_symex = true;
    return;
  }

  // put a copy of the current state into the state-queue, to be used by
  // merge_gotos when we visit new_state_pc
  framet::goto_state_listt &goto_state_list =
    state.call_stack().top().goto_state_map[new_state_pc];

  // On an unconditional GOTO we don't need our state, as it will be overwritten
  // by merge_goto. Therefore we move it onto goto_state_list instead of copying
  // as usual.
  if(new_guard.is_true())
  {
    // The move here only moves goto_statet, the base class of goto_symex_statet
    // and not the entire thing.
    goto_state_list.emplace_back(state.source, std::move(state));

    symex_transition(state, state_pc, backward);

    state.guard = guardt(false_exprt(), guard_manager);
    state.reachable = false;
  }
  else
  {
    goto_state_list.emplace_back(state.source, state);

    symex_transition(state, state_pc, backward);

    if(!symex_config.doing_path_exploration)
    {
      // This doesn't work for --paths (single-path mode) yet, as in multi-path
      // mode we remove the implied constants at a control-flow merge, but in
      // single-path mode we don't run merge_gotos.
      auto &taken_state = backward ? state : goto_state_list.back().second;
      auto &not_taken_state = backward ? goto_state_list.back().second : state;

      apply_goto_condition(
        state,
        taken_state,
        not_taken_state,
        instruction.condition(),
        new_guard,
        ns);
    }

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
      symbol_exprt guard_symbol_expr =
        symbol_exprt(statet::guard_identifier(), bool_typet());
      exprt new_rhs = boolean_negate(new_guard);

      ssa_exprt new_lhs =
        state.rename_ssa<L1>(ssa_exprt{guard_symbol_expr}, ns).get();
      new_lhs =
        state.assignment(std::move(new_lhs), new_rhs, ns, true, false).get();

      guardt guard{true_exprt{}, guard_manager};

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

      guard_expr = state.rename(boolean_negate(guard_symbol_expr), ns).get();
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
      goto_statet &new_state = goto_state_list.back().second;
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

void goto_symext::symex_unreachable_goto(statet &state)
{
  PRECONDITION(!state.reachable);
  // This is like symex_goto, except the state is unreachable. We try to take
  // some arbitrary choice that maintains the state guard in a reasonable state
  // in order that it simplifies properly when states are merged (in
  // merge_gotos). Note we can't try to evaluate the actual GOTO guard because
  // our constant propagator might be out of date, since we haven't been
  // executing assign instructions.

  // If the guard is already false then there's no value in this state; just
  // carry on and check the next instruction.
  if(state.guard.is_false())
  {
    symex_transition(state);
    return;
  }

  const goto_programt::instructiont &instruction = *state.source.pc;
  PRECONDITION(instruction.is_goto());
  goto_programt::const_targett goto_target = instruction.get_target();

  auto queue_unreachable_state_at_target = [&]() {
    framet::goto_state_listt &goto_state_list =
      state.call_stack().top().goto_state_map[goto_target];
    goto_statet new_state(state.guard_manager);
    new_state.guard = state.guard;
    new_state.reachable = false;
    goto_state_list.emplace_back(state.source, std::move(new_state));
  };

  if(instruction.condition().is_true())
  {
    if(instruction.is_backwards_goto())
    {
      // Give up trying to salvage the guard
      // (this state's guard is squashed, without queueing it at the target)
    }
    else
    {
      // Take the branch:
      queue_unreachable_state_at_target();
    }

    state.guard.add(false_exprt());
  }
  else
  {
    // Arbitrarily assume a conditional branch is not-taken, except for when
    // there's an incoming backedge, when we guess that the taken case is less
    // likely to lead to that backedge than the not-taken case.
    bool maybe_loop_head = std::any_of(
      instruction.incoming_edges.begin(),
      instruction.incoming_edges.end(),
      [&instruction](const goto_programt::const_targett predecessor) {
        return predecessor->location_number > instruction.location_number;
      });

    if(instruction.is_backwards_goto() || !maybe_loop_head)
    {
      // Assume branch not taken (fall through)
    }
    else
    {
      // Assume branch taken:
      queue_unreachable_state_at_target();
      state.guard.add(false_exprt());
    }
  }

  symex_transition(state);
}

bool goto_symext::check_break(const irep_idt &loop_id, unsigned unwind)
{
  // dummy implementation
  return false;
}

void goto_symext::merge_gotos(statet &state)
{
  framet &frame = state.call_stack().top();

  // first, see if this is a target at all
  auto state_map_it = frame.goto_state_map.find(state.source.pc);

  if(state_map_it==frame.goto_state_map.end())
    return; // nothing to do

  // we need to merge
  framet::goto_state_listt &state_list = state_map_it->second;

  for(auto list_it = state_list.rbegin(); list_it != state_list.rend();
      ++list_it)
  {
    merge_goto(list_it->first, std::move(list_it->second), state);
  }

  // clean up to save some memory
  frame.goto_state_map.erase(state_map_it);
}

static guardt
merge_state_guards(goto_statet &goto_state, goto_symex_statet &state)
{
  // adjust guard, even using guards from unreachable states. This helps to
  // shrink the state guard if the incoming edge is from a path that was
  // truncated by config.unwind, config.depth or an assume-false instruction.

  // Note when an unreachable state contributes its guard, merging it in is
  // optional, since the formula already implies the unreachable guard is
  // impossible. Therefore we only integrate it when to do so simplifies the
  // state guard.

  // This function can trash either state's guards, since goto_state is dying
  // and state's guard will shortly be overwritten.

  if(
    (goto_state.reachable && state.reachable) ||
    state.guard.disjunction_may_simplify(goto_state.guard))
  {
    state.guard |= goto_state.guard;
    return std::move(state.guard);
  }
  else if(!state.reachable && goto_state.reachable)
  {
    return std::move(goto_state.guard);
  }
  else
  {
    return std::move(state.guard);
  }
}

void goto_symext::merge_goto(
  const symex_targett::sourcet &,
  goto_statet &&goto_state,
  statet &state)
{
  // check atomic section
  if(state.atomic_section_id != goto_state.atomic_section_id)
    throw incorrect_goto_program_exceptiont(
      "atomic sections differ across branches",
      state.source.pc->source_location());

  // Merge guards. Don't write this to `state` yet because we might move
  // goto_state over it below.
  guardt new_guard = merge_state_guards(goto_state, state);

  // Merge constant propagator, value-set etc. only if the incoming state is
  // reachable:
  if(goto_state.reachable)
  {
    if(!state.reachable)
    {
      // Important to note that we're moving into our base class here.
      // Note this overwrites state.guard, but we restore it below.
      static_cast<goto_statet &>(state) = std::move(goto_state);
    }
    else
    {
      // do SSA phi functions
      phi_function(goto_state, state);

      // merge value sets
      state.value_set.make_union(goto_state.value_set);

      // adjust depth
      state.depth = std::min(state.depth, goto_state.depth);
    }
  }

  // Save the new state guard
  state.guard = std::move(new_guard);
}

/// Helper function for \c phi_function which merges the names of an identifier
/// for two different states.
/// \param goto_state: first state
/// \param [in, out] dest_state: second state
/// \param ns: namespace
/// \param diff_guard: difference between the guards of the two states
/// \param [out] log: logger for debug messages
/// \param do_simplify: should the right-hand-side of the assignment that is
///   added to the target be simplified
/// \param [out] target: equation that will receive the resulting assignment
/// \param dirty: dirty-object analysis
/// \param ssa: SSA expression to merge
/// \param goto_count: current level 2 count in \p goto_state of
///   \p l1_identifier
/// \param dest_count: level 2 count in \p dest_state of \p l1_identifier
static void merge_names(
  const goto_statet &goto_state,
  goto_symext::statet &dest_state,
  const namespacet &ns,
  const guardt &diff_guard,
  messaget &log,
  const bool do_simplify,
  symex_target_equationt &target,
  const incremental_dirtyt &dirty,
  const ssa_exprt &ssa,
  const unsigned goto_count,
  const unsigned dest_count)
{
  const irep_idt l1_identifier = ssa.get_identifier();
  const irep_idt &obj_identifier = ssa.get_object_name();

  if(obj_identifier == goto_symext::statet::guard_identifier())
    return; // just a guard, don't bother

  if(goto_count == dest_count)
    return; // not at all changed

  // changed - but only on a branch that is now dead, and the other branch is
  // uninitialized/invalid
  if(
    (!dest_state.reachable && goto_count == 0) ||
    (!goto_state.reachable && dest_count == 0))
  {
    return;
  }

  // field sensitivity: only merge on individual fields
  if(dest_state.field_sensitivity.is_divisible(ssa))
    return;

  // shared variables are renamed on every access anyway, we don't need to
  // merge anything
  const symbolt &symbol = ns.lookup(obj_identifier);

  // shared?
  if(
    dest_state.atomic_section_id == 0 && dest_state.threads.size() >= 2 &&
    (symbol.is_shared() || dirty(symbol.name)))
  {
    return; // no phi nodes for shared stuff
  }

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

    if(p_it.has_value())
      goto_state_rhs = *p_it;
    else
      to_ssa_expr(goto_state_rhs).set_level_2(goto_count);
  }

  {
    const auto p_it = dest_state.propagation.find(l1_identifier);

    if(p_it.has_value())
      dest_state_rhs = *p_it;
    else
      to_ssa_expr(dest_state_rhs).set_level_2(dest_count);
  }

  exprt rhs;

  // Don't add a conditional to the assignment when:
  //  1. Either guard is false, so we can't follow that branch.
  //  2. Either identifier is of generation zero, and so hasn't been
  //     initialized and therefore an invalid target.

  // These rules only apply to dynamic objects and locals.
  if(!dest_state.reachable)
    rhs = goto_state_rhs;
  else if(!goto_state.reachable)
    rhs = dest_state_rhs;
  else if(goto_count == 0)
    rhs = dest_state_rhs;
  else if(dest_count == 0)
    rhs = goto_state_rhs;
  else
  {
    rhs = if_exprt(diff_guard.as_expr(), goto_state_rhs, dest_state_rhs);
    if(do_simplify)
      simplify(rhs, ns);
  }

  dest_state.record_events.push(false);
  const ssa_exprt new_lhs =
    dest_state.assignment(ssa, rhs, ns, true, true).get();
  dest_state.record_events.pop();

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
  const goto_statet &goto_state,
  statet &dest_state)
{
  if(
    goto_state.get_level2().current_names.empty() &&
    dest_state.get_level2().current_names.empty())
    return;

  guardt diff_guard = goto_state.guard;
  // this gets the diff between the guards
  diff_guard -= dest_state.guard;

  symex_renaming_levelt::delta_viewt delta_view;
  goto_state.get_level2().current_names.get_delta_view(
    dest_state.get_level2().current_names, delta_view, false);

  for(const auto &delta_item : delta_view)
  {
    const ssa_exprt &ssa = delta_item.m.first;
    unsigned goto_count = delta_item.m.second;
    unsigned dest_count = !delta_item.is_in_both_maps()
                            ? 0
                            : delta_item.get_other_map_value().second;

    merge_names(
      goto_state,
      dest_state,
      ns,
      diff_guard,
      log,
      symex_config.simplify_opt,
      target,
      path_storage.dirty,
      ssa,
      goto_count,
      dest_count);
  }

  delta_view.clear();
  dest_state.get_level2().current_names.get_delta_view(
    goto_state.get_level2().current_names, delta_view, false);

  for(const auto &delta_item : delta_view)
  {
    if(delta_item.is_in_both_maps())
      continue;

    const ssa_exprt &ssa = delta_item.m.first;
    unsigned goto_count = 0;
    unsigned dest_count = delta_item.m.second;

    merge_names(
      goto_state,
      dest_state,
      ns,
      diff_guard,
      log,
      symex_config.simplify_opt,
      target,
      path_storage.dirty,
      ssa,
      goto_count,
      dest_count);
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

  if(symex_config.unwinding_assertions)
  {
    // Generate VCC for unwinding assertion.
    vcc(
      negated_cond,
      "unwinding assertion loop " + std::to_string(loop_number),
      state);
  }

  if(!symex_config.partial_loops)
  {
    // generate unwinding assumption, unless we permit partial loops
    symex_assume_l2(state, negated_cond);
  }
}

bool goto_symext::should_stop_unwind(
  const symex_targett::sourcet &,
  const call_stackt &,
  unsigned)
{
  // by default, we keep going
  return false;
}
