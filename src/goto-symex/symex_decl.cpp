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

  // just do the L1 renaming to preserve locality
  const irep_idt &l0_identifier=to_symbol_expr(code.op0()).get_identifier();

  irep_idt l1_identifier;

  do
  {
    unsigned index=state.top().level1.current_names[l0_identifier];
    state.top().level1.rename(l0_identifier, index+1);
    l1_identifier=state.top().level1(l0_identifier);
  }
  while(state.declaration_history.find(l1_identifier)!=
        state.declaration_history.end());
  
  // forget the old L2 renaming to avoid SSA for it
  state.level2.remove(l1_identifier);
  state.propagation.remove(l1_identifier);
  state.declaration_history.insert(l1_identifier); 
  
  state.top().local_variables.insert(l1_identifier);
    
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
    state.guard,
    ssa_lhs, original_lhs,
    state.source);
}
