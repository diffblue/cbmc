/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/find_symbols.h>
#include <util/std_expr.h>

#include <pointer-analysis/add_failed_symbols.h>

void goto_symext::symex_dead(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const code_deadt &code = instruction.get_dead();

  ssa_exprt ssa = state.rename_ssa<L1>(ssa_exprt{code.symbol()}, ns).get();

  const exprt fields = state.field_sensitivity.get_fields(ns, state, ssa);
  find_symbols_sett fields_set;
  find_symbols(fields, fields_set);

  for(const irep_idt &l1_identifier : fields_set)
  {
    // We cannot remove the object from the L1 renaming map, because L1 renaming
    // information is not local to a path, but removing it from the propagation
    // map and value-set is safe as 1) it is local to a path and 2) this
    // instance can no longer appear.
    if(state.value_set.values.has_key(l1_identifier))
      state.value_set.values.erase(l1_identifier);
    state.propagation.erase(l1_identifier);
    // Remove from the local L2 renaming map; this means any reads from the dead
    // identifier will use generation 0 (e.g. x!N@M#0, where N and M are
    // positive integers), which is never defined by any write, and will be
    // dropped by `goto_symext::merge_goto` on merging with branches where the
    // identifier is still live.
    state.drop_l1_name(l1_identifier);
  }
}
