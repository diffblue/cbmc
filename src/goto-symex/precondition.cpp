/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <find_symbols.h>

#include <pointer-analysis/goto_program_dereference.h>

#include "goto_symex_state.h"
#include "precondition.h"

/*******************************************************************\

   Class: preconditiont

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class preconditiont
{
public:
  preconditiont(
    const namespacet &_ns,
    value_setst &_value_sets,
    const goto_programt::const_targett _target,
    const symex_target_equationt::SSA_stept &_SSA_step,
    const goto_symex_statet &_s):
    ns(_ns),
    value_sets(_value_sets),
    target(_target),
    SSA_step(_SSA_step),
    s(_s)
  {
  }

protected:
  const namespacet &ns;
  value_setst &value_sets;
  const goto_programt::const_targett target;
  const symex_target_equationt::SSA_stept &SSA_step;
  const goto_symex_statet &s;
  void compute_rec(exprt &dest);

public:
  void compute(exprt &dest);
  
protected:
  void compute_address_of(exprt &dest);
};

/*******************************************************************\

Function: precondition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void precondition(
  const namespacet &ns,
  value_setst &value_sets,
  const goto_programt::const_targett target,
  const symex_target_equationt &equation,
  const goto_symex_statet &s,
  exprt &dest)
{
  for(symex_target_equationt::SSA_stepst::const_reverse_iterator
      it=equation.SSA_steps.rbegin();
      it!=equation.SSA_steps.rend();
      it++)
  {
    preconditiont precondition(ns, value_sets, target, *it, s);
    precondition.compute(dest);
    if(dest.is_false()) return;
  }
}

/*******************************************************************\

Function: preconditiont::compute_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void preconditiont::compute_address_of(exprt &dest)
{
  if(dest.id()==ID_symbol)
  {
    // leave alone
  }
  else if(dest.id()==ID_index)
  {
    assert(dest.operands().size()==2);
    compute_address_of(dest.op0());
    compute(dest.op1());
  }
  else if(dest.id()==ID_member)
  {
    assert(dest.operands().size()==1);
    compute_address_of(dest.op0());
  }
  else if(dest.id()==ID_dereference)
  {
    assert(dest.operands().size()==1);
    compute(dest.op0());
  }
}

/*******************************************************************\

Function: preconditiont::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void preconditiont::compute(exprt &dest)
{
  compute_rec(dest);
}

/*******************************************************************\

Function: preconditiont::compute_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void preconditiont::compute_rec(exprt &dest)
{
  if(dest.id()==ID_address_of)
  {
    // only do index!
    assert(dest.operands().size()==1);
    compute_address_of(dest.op0());
  }
  else if(dest.id()==ID_symbol)
  {
    if(dest.get(ID_identifier)==
       s.get_original_name(SSA_step.ssa_lhs.get_identifier()))
    {
      dest=SSA_step.ssa_rhs;
      s.get_original_name(dest);
    }
  }
  else if(dest.id()==ID_dereference)
  {
    assert(dest.operands().size()==1);

    const irep_idt &lhs_identifier=
      s.get_original_name(SSA_step.ssa_lhs.get_identifier());
  
    // aliasing may happen here

    value_setst::valuest expr_set;
    value_sets.get_values(target, dest.op0(), expr_set);
    hash_set_cont<irep_idt, irep_id_hash> symbols;

    for(value_setst::valuest::const_iterator
        it=expr_set.begin();
        it!=expr_set.end();
        it++)
      find_symbols(*it, symbols);
    
    if(symbols.find(lhs_identifier)!=symbols.end())
    {
      // may alias!
      exprt tmp;
      tmp.swap(dest.op0());
      dereference(target, tmp, ns, value_sets);
      dest.swap(tmp);
      compute_rec(dest);
    }
    else
    {
      // nah, ok
      compute_rec(dest.op0());
    }
  }
  else
    Forall_operands(it, dest)
      compute_rec(*it);
}
