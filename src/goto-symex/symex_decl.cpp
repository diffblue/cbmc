/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <cassert>

#include <util/std_expr.h>

void goto_symext::symex_decl(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const auto &code = instruction.get_decl();

  // two-operand decl not supported here
  // we handle the decl with only one operand
  PRECONDITION(code.operands().size() == 1);

  symex_decl(state, code.symbol());
}

void goto_symext::symex_decl(statet &state, const symbol_exprt &expr)
{
  // each declaration introduces a new object, which we record as a fresh L1
  // index

  // We use "1" as the first level-1 index, which is in line with doing so for
  // level-2 indices (but it's an arbitrary choice, we have just always been
  // doing it this way).
  ssa_exprt ssa = state.add_object(
    expr,
    [this](const irep_idt &l0_name) {
      return path_storage.get_unique_l1_index(l0_name, 1);
    },
    ns);

  ssa = state.declare(std::move(ssa), ns);

  // we hide the declaration of auxiliary variables
  // and if the statement itself is hidden
  bool hidden = ns.lookup(expr.get_identifier()).is_auxiliary ||
                state.call_stack().top().hidden_function ||
                state.source.pc->source_location.get_hide();

  target.decl(
    state.guard.as_expr(),
    ssa,
    state.field_sensitivity.apply(ns, state, ssa, false),
    state.source,
    hidden ? symex_targett::assignment_typet::HIDDEN
           : symex_targett::assignment_typet::STATE);

  if(path_storage.dirty(ssa.get_object_name()) && state.atomic_section_id == 0)
    target.shared_write(
      state.guard.as_expr(),
      ssa,
      state.atomic_section_id,
      state.source);
}
