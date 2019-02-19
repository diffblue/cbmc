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

  const code_deadt &code = instruction.get_dead();

  // We increase the L2 renaming to make these non-deterministic.
  // We also prevent propagation of old values.

  ssa_exprt ssa = state.rename_level1_ssa(ssa_exprt{code.symbol()}, ns);

  // in case of pointers, put something into the value set
  if(code.symbol().type().id() == ID_pointer)
  {
    exprt rhs;
    if(auto failed = get_failed_symbol(to_symbol_expr(code.symbol()), ns))
      rhs = address_of_exprt(*failed, to_pointer_type(code.symbol().type()));
    else
      rhs=exprt(ID_invalid);

    state.rename<goto_symex_statet::L1>(rhs, ns);
    state.value_set.assign(ssa, rhs, ns, true, false);
  }

  const irep_idt &l1_identifier = ssa.get_identifier();

  // prevent propagation
  state.propagation.erase(l1_identifier);

  // L2 renaming
  auto level2_it = state.level2.current_names.find(l1_identifier);
  if(level2_it != state.level2.current_names.end())
    symex_renaming_levelt::increase_counter(level2_it);
}
