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

void goto_symext::symex_dead(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const code_deadt &code = to_code_dead(instruction.code);

  // We increase the L2 renaming to make these non-deterministic.
  // We also prevent propagation of old values.

  ssa_exprt ssa(code.symbol());
  state.rename(ssa, ns, goto_symex_statet::L1);

  // in case of pointers, put something into the value set
  if(ns.follow(code.symbol().type()).id() == ID_pointer)
  {
    exprt failed = get_failed_symbol(to_symbol_expr(code.symbol()), ns);

    exprt rhs;

    if(failed.is_not_nil())
      rhs = address_of_exprt(failed, to_pointer_type(code.symbol().type()));
    else
      rhs=exprt(ID_invalid);

    state.rename(rhs, ns, goto_symex_statet::L1);
    state.value_set.assign(ssa, rhs, ns, true, false);
  }

  ssa_exprt ssa_lhs=to_ssa_expr(ssa);
  const irep_idt &l1_identifier=ssa_lhs.get_identifier();

  // prevent propagation
  state.propagation.erase(l1_identifier);

  // L2 renaming
  auto level2_it = state.level2.current_names.find(l1_identifier);
  if(level2_it != state.level2.current_names.end())
    symex_renaming_levelt::increase_counter(level2_it);
}
