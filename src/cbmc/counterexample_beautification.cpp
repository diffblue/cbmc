/*******************************************************************\

Module: Counterexample Beautification using Incremental SAT

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "counterexample_beautification.h"

/*******************************************************************\

Function: counterexample_beautificationt::get_minimization_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautificationt::get_minimization_symbols(
  const bv_cbmct &bv_cbmc,
  const symex_target_equationt &equation,
  const symex_target_equationt::SSA_stepst::const_iterator failed,
  minimization_symbolst &minimization_symbols)
{
  // remove the ones that are assigned under false guards

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
  {
    if(it->is_assignment() &&
       it->assignment_type==symex_targett::STATE)
    {
      if(!bv_cbmc.prop.l_get(it->guard_literal).is_false())
        if(it->original_lhs_object.type()!=bool_typet())
          minimization_symbols.insert(it->ssa_lhs);
    }

    // reached failed assertion?
    if(it==failed)
      break;
  }
}

/*******************************************************************\

Function: counterexample_beautificationt::get_failed_claim

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symex_target_equationt::SSA_stepst::const_iterator
counterexample_beautificationt::get_failed_claim(
  const bv_cbmct &bv_cbmc,
  const symex_target_equationt &equation)
{
  // find failed claim

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
    if(it->is_assert() &&
       bv_cbmc.prop.l_get(it->guard_literal).is_true() &&
       bv_cbmc.prop.l_get(it->cond_literal).is_false())
      return it;
  
  assert(false);
  return equation.SSA_steps.end();
}
