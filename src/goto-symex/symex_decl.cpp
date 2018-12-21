/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <cassert>

#include <util/std_expr.h>

#include <analyses/dirty.h>

void goto_symext::symex_decl(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const codet &code = instruction.code;

  // two-operand decl not supported here
  // we handle the decl with only one operand
  PRECONDITION(code.operands().size() == 1);

  symex_decl(state, to_code_decl(code).symbol());
}

void goto_symext::symex_decl(statet &state, const symbol_exprt &expr)
{
  // We increase the L2 renaming to make these non-deterministic.
  // We also prevent propagation of old values.

  ssa_exprt ssa(expr);
  state.rename(ssa, ns, goto_symex_statet::L1);
  const irep_idt &l1_identifier=ssa.get_identifier();

  // rename type to L2
  state.rename(ssa.type(), l1_identifier, ns);
  ssa.update_type();

<<<<<<< HEAD
  // in case of pointers, put something into the value set
  if(ns.follow(expr.type()).id()==ID_pointer)
  {
    exprt failed=
      get_failed_symbol(expr, ns);

    exprt rhs;

    if(failed.is_not_nil())
      rhs=address_of_exprt(failed, to_pointer_type(expr.type()));
    else
      rhs=exprt(ID_invalid);

    state.rename(rhs, ns, goto_symex_statet::L1);
    state.value_set.assign(ssa, rhs, ns, true, false);
  }

  // prevent propagation
  state.propagation.erase(l1_identifier);

  // L2 renaming
  // inlining may yield multiple declarations of the same identifier
  // within the same L1 context
  const auto level2_it =
    state.level2.current_names.emplace(l1_identifier, std::make_pair(ssa, 0))
      .first;
  symex_renaming_levelt::increase_counter(level2_it);
  const bool record_events=state.record_events;
  state.record_events=false;
  state.rename(ssa, ns);
  state.record_events=record_events;
=======
  // L2 renaming
  // inlining may yield multiple declarations of the same identifier
  // within the same L1 context
  if(state.level2.current_names.find(l1_identifier)==
     state.level2.current_names.end())
    state.level2.current_names[l1_identifier]=std::make_pair(ssa, 0);
  init_l1 = l1_identifier;

  // optimisation: skip non-deterministic initialisation if the next instruction
  // will take care of initialisation (but ensure int x=x; is handled properly)
  goto_programt::const_targett next = std::next(state.source.pc);
  if(
    next->is_assign() && to_code_assign(next->code).lhs() == expr &&
    to_code_assign(next->code).rhs().is_constant())
  {
    return;
  }
>>>>>>> 2846e8c... Explicitly initialise non-static objects with non-deterministic values

  // we hide the declaration of auxiliary variables
  // and if the statement itself is hidden
  bool hidden=
    ns.lookup(expr.get_identifier()).is_auxiliary ||
    state.top().hidden_function ||
    state.source.pc->source_location.get_hide();

  side_effect_expr_nondett init(ssa.type());
  replace_nondet(init);

  guardt guard;
  symex_assign_symbol(
    state,
    ssa,
    nil_exprt(),
    init,
    guard,
    hidden?
      symex_targett::assignment_typet::HIDDEN:
      symex_targett::assignment_typet::STATE);

  if(state.dirty(ssa.get_object_name()) && state.atomic_section_id == 0)
    target.shared_write(
      state.guard.as_expr(),
      ssa,
      state.atomic_section_id,
      state.source);
}
