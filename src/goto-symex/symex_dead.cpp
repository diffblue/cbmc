/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <util/std_expr.h>

void goto_symext::symex_dead(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;
  symex_dead(state, instruction.dead_symbol());
}

static void remove_l1_object_rec(
  goto_symext::statet &state,
  const exprt &l1_expr,
  const namespacet &ns)
{
  if(is_ssa_expr(l1_expr))
  {
    const ssa_exprt &l1_ssa = to_ssa_expr(l1_expr);
    const irep_idt &l1_identifier = l1_ssa.get_identifier();

    // We cannot remove the object from the L1 renaming map, because L1 renaming
    // information is not local to a path, but removing it from the propagation
    // map and value-set is safe as 1) it is local to a path and 2) this
    // instance can no longer appear (unless shared across threads).
    if(
      state.threads.size() <= 1 ||
      state.write_is_shared(l1_ssa, ns) ==
        goto_symex_statet::write_is_shared_resultt::NOT_SHARED)
    {
      state.value_set.values.erase_if_exists(l1_identifier);
    }
    state.propagation.erase_if_exists(l1_identifier);
    // Remove from the local L2 renaming map; this means any reads from the dead
    // identifier will use generation 0 (e.g. x!N@M#0, where N and M are
    // positive integers), which is never defined by any write, and will be
    // dropped by `goto_symext::merge_goto` on merging with branches where the
    // identifier is still live.
    state.drop_l1_name(l1_identifier);
  }
  else if(l1_expr.id() == ID_array || l1_expr.id() == ID_struct)
  {
    for(const auto &op : l1_expr.operands())
      remove_l1_object_rec(state, op, ns);
  }
  else
    UNREACHABLE;
}

void goto_symext::symex_dead(statet &state, const symbol_exprt &symbol_expr)
{
  ssa_exprt to_rename = is_ssa_expr(symbol_expr) ? to_ssa_expr(symbol_expr)
                                                 : ssa_exprt{symbol_expr};
  ssa_exprt ssa = state.rename_ssa<L1>(to_rename, ns).get();

  const exprt fields = state.field_sensitivity.get_fields(ns, state, ssa);
  remove_l1_object_rec(state, fields, ns);
}
