/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <cassert>

#include <util/std_expr.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <analyses/dirty.h>

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

  ssa_exprt ssa = state.rename_ssa<L0>(ssa_exprt{expr}, ns);
  // We use "1" as the first level-1 index, which is in line with doing so for
  // level-2 indices (but it's an arbitrary choice, we have just always been
  // doing it this way).
  const std::size_t fresh_l1_index =
    path_storage.get_unique_index(ssa.get_identifier(), 1);
  state.add_object(ssa, fresh_l1_index, ns);
  const irep_idt &l1_identifier = ssa.get_identifier();

  // rename type to L2
  state.rename(ssa.type(), l1_identifier, ns);
  ssa.update_type();

  // in case of pointers, put something into the value set
  if(expr.type().id() == ID_pointer)
  {
    exprt rhs;
    if(auto failed = get_failed_symbol(expr, ns))
      rhs = address_of_exprt(*failed, to_pointer_type(expr.type()));
    else
      rhs=exprt(ID_invalid);

    exprt l1_rhs = state.rename<L1>(std::move(rhs), ns);
    state.value_set.assign(ssa, l1_rhs, ns, true, false);
  }

  // L2 renaming
  bool is_new =
    state.level2.current_names.emplace(l1_identifier, std::make_pair(ssa, 1))
      .second;
  CHECK_RETURN(is_new);
  const bool record_events=state.record_events;
  state.record_events=false;
  exprt expr_l2 = state.rename(std::move(ssa), ns);
  INVARIANT(
    expr_l2.id() == ID_symbol && expr_l2.get_bool(ID_C_SSA_symbol),
    "symbol to declare should not be replaced by constant propagation");
  ssa = to_ssa_expr(expr_l2);
  state.record_events=record_events;

  // we hide the declaration of auxiliary variables
  // and if the statement itself is hidden
  bool hidden = ns.lookup(expr.get_identifier()).is_auxiliary ||
                state.call_stack().top().hidden_function ||
                state.source.pc->source_location.get_hide();

  target.decl(
    state.guard.as_expr(),
    ssa,
    state.source,
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
