/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <expr_util.h>
#include <rename.h>

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
  const irep_idt &identifier=code.op0().get(ID_identifier);

  irep_idt l1_identifier=state.top().level1(identifier);

  // forget the old l2 renaming to avoid SSA for it
  state.level2.remove(l1_identifier);

  // increase the frame if we have seen this declaration before
  while(state.declaration_history.find(l1_identifier)!=
        state.declaration_history.end())
  {
    unsigned index=state.top().level1.current_names[identifier];
    state.top().level1.rename(identifier, index+1);
    l1_identifier=state.top().level1(identifier);
  }

  state.declaration_history.insert(l1_identifier); 
  
  state.top().local_variables.insert(l1_identifier);
    
  // seen it before?
  // it should get a fresh value in any case
  statet::level2t::current_namest::iterator it=
    state.level2.current_names.find(l1_identifier);
  
  if(it!=state.level2.current_names.end())
  {
    state.level2.rename(l1_identifier, it->second.count+1);
    it->second.constant.make_nil();
  }
  
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
    state.value_set.assign(l1_lhs, rhs, ns);
  }
}
