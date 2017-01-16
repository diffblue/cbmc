/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/rename.h>
#include <util/std_expr.h>

#include <pointer-analysis/add_failed_symbols.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_dead

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_dead(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const codet &code=to_code(instruction.code);

  if(code.operands().size()!=1)
    throw "dead expects one operand";

  if(code.op0().id()!=ID_symbol)
    throw "dead expects symbol as first operand";

  // We increase the L2 renaming to make these non-deterministic.
  // We also prevent propagation of old values.

  ssa_exprt ssa(to_symbol_expr(code.op0()));
  state.rename(ssa, ns, goto_symex_statet::L1);

  // in case of pointers, put something into the value set
  if(ns.follow(code.op0().type()).id()==ID_pointer)
  {
    exprt failed=
      get_failed_symbol(to_symbol_expr(code.op0()), ns);

    exprt rhs;

    if(failed.is_not_nil())
    {
      address_of_exprt address_of_expr;
      address_of_expr.object()=failed;
      address_of_expr.type()=code.op0().type();
      rhs=address_of_expr;
    }
    else
      rhs=exprt(ID_invalid);

    state.rename(rhs, ns, goto_symex_statet::L1);
    state.value_set.assign(ssa, rhs, ns, true, false);
  }

  ssa_exprt ssa_lhs=to_ssa_expr(ssa);
  const irep_idt &l1_identifier=ssa_lhs.get_identifier();

  // prevent propagation
  state.propagation.remove(l1_identifier);

  // L2 renaming
  if(state.level2.current_names.find(l1_identifier)!=
     state.level2.current_names.end())
    state.level2.increase_counter(l1_identifier);
}
