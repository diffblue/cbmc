/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <expr_util.h>
#include <rename.h>
#include <std_expr.h>

#include <pointer-analysis/add_failed_symbols.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::symex_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_decl(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const codet &code=to_code(instruction.code);

  if(code.operands().size()==2)
    throw "two-operand decl not supported here";

  if(code.operands().size()!=1)
    throw "decl expects one operand";
  
  if(code.op0().id()!=ID_symbol)
    throw "decl expects symbol as first operand";

  // We increase the L2 renaming to make these non-deterministic.
  // We also prevent propagation of old values.
  
  const irep_idt &identifier=
    to_symbol_expr(code.op0()).get_identifier();
    
  const irep_idt l1_identifier=
    state.rename(identifier, ns, goto_symex_statet::L1);
    
  // prevent propagation
  state.propagation.remove(l1_identifier);

  // L2 renaming
  unsigned new_count=state.level2.current_count(l1_identifier)+1;
  state.level2.rename(l1_identifier, new_count);
    
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
    
    symbol_exprt l1_lhs;
    l1_lhs.type()=code.op0().type();
    l1_lhs.set_identifier(l1_identifier);
    state.rename(rhs, ns, goto_symex_statet::L1);
    state.value_set.assign(l1_lhs, rhs, ns);
  }
  
  // record the declaration
  symbol_exprt original_lhs=to_symbol_expr(code.op0());
  symbol_exprt ssa_lhs=original_lhs;
  state.rename(ssa_lhs, ns);
  
  target.decl(
    state.guard.as_expr(),
    ssa_lhs, original_lhs,
    state.source);
}
