/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <find_symbols.h>
#include <expr_util.h>
#include <std_expr.h>

#include "goto_symex_state.h"
#include "postcondition.h"

/*******************************************************************\

   Class: postconditiont

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class postconditiont
{
public:
  postconditiont(
    const namespacet &_ns,
    const value_sett &_value_set,
    const symex_target_equationt::SSA_stept &_SSA_step,
    const goto_symex_statet &_s):
    ns(_ns),
    value_set(_value_set),
    SSA_step(_SSA_step),
    s(_s)
  {
  }

protected:
  const namespacet &ns;
  const value_sett &value_set;
  const symex_target_equationt::SSA_stept &SSA_step;
  const goto_symex_statet &s;

public:
  void compute(exprt &dest);
  
protected:
  void strengthen(exprt &dest);
  void weaken(exprt &dest);
  bool is_used_address_of(const exprt &expr, const irep_idt &identifier);
  bool is_used(const exprt &expr, const irep_idt &identifier);
};

/*******************************************************************\

Function: postcondition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void postcondition(
  const namespacet &ns,
  const value_sett &value_set,
  const symex_target_equationt &equation,
  const goto_symex_statet &s,
  exprt &dest)
{
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    postconditiont postcondition(ns, value_set, *it, s);
    postcondition.compute(dest);
    if(dest.is_false()) return;
  }
}

/*******************************************************************\

Function: postconditiont::is_used_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool postconditiont::is_used_address_of(
  const exprt &expr,
  const irep_idt &identifier)
{
  if(expr.id()==ID_symbol)
  {
    // leave alone
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);

    return
      is_used_address_of(expr.op0(), identifier) ||
      is_used(expr.op1(), identifier);
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    return is_used_address_of(expr.op0(), identifier);
  }
  else if(expr.id()==ID_dereference)
  {
    assert(expr.operands().size()==1);
    return is_used(expr.op0(), identifier);
  }
  
  return false;
}

/*******************************************************************\

Function: postconditiont::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void postconditiont::compute(exprt &dest)
{
  // weaken due to assignment
  weaken(dest);
  
  // strengthen due to assignment
  strengthen(dest);
}

/*******************************************************************\

Function: postconditiont::strengthen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void postconditiont::weaken(exprt &dest)
{
  if(dest.id()==ID_and &&
     dest.type()==bool_typet()) // this distributes over "and"
  {
    Forall_operands(it, dest)
      weaken(*it);
      
    return;
  }

  // we are lazy:
  // if lhs is mentioned in dest, we use "true".
  
  const irep_idt &lhs_identifier=
    s.get_original_name(SSA_step.ssa_lhs.get_identifier());

  if(is_used(dest, lhs_identifier))
    dest.make_true();
    
  // otherwise, no weakening needed
}  

/*******************************************************************\

Function: postconditiont::strengthen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void postconditiont::strengthen(exprt &dest)
{
  const irep_idt &lhs_identifier=
    s.get_original_name(SSA_step.ssa_lhs.get_identifier());

  if(!is_used(SSA_step.ssa_rhs, lhs_identifier))
  {
    // we don't do arrays or structs
    if(SSA_step.ssa_lhs.type().id()==ID_array ||
       SSA_step.ssa_lhs.type().id()==ID_struct)
      return;
  
    equal_exprt equality(SSA_step.ssa_lhs, SSA_step.ssa_rhs);
    s.get_original_name(equality);

    if(dest.is_true())
      dest.swap(equality);
    else
      dest=gen_and(dest, equality);
  }
}  

/*******************************************************************\

Function: postconditiont::is_used

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool postconditiont::is_used(
  const exprt &expr,
  const irep_idt &identifier)
{
  if(expr.id()==ID_address_of)
  {
    // only do index!
    assert(expr.operands().size()==1);
    return is_used_address_of(expr.op0(), identifier);
  }
  else if(expr.id()==ID_symbol)
  {
    return s.get_original_name(expr.get(ID_identifier))==identifier;
  }
  else if(expr.id()==ID_dereference)
  {
    assert(expr.operands().size()==1);

    // aliasing may happen here

    value_setst::valuest expr_set;
    value_set.get_value_set(expr.op0(), expr_set, ns);
    hash_set_cont<irep_idt, irep_id_hash> symbols;
    
    for(value_setst::valuest::const_iterator
        it=expr_set.begin();
        it!=expr_set.end();
        it++)
    {
      exprt tmp(*it);
      s.get_original_name(tmp);
      find_symbols(tmp, symbols);
    }
    
    return symbols.find(identifier)!=symbols.end();
  }
  else
    forall_operands(it, expr)
      if(is_used(*it, identifier))
        return true;
        
  return false;
}
