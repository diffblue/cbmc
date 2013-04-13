/*******************************************************************\

Module: Counterexample Beautification using Incremental SAT

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/threeval.h>
#include <util/bitvector.h>
#include <util/expr_util.h>
#include <util/arith_tools.h>
#include <util/symbol.h>

#include <solvers/prop/minimize.h>

#include "counterexample_beautification.h"

/*******************************************************************\

Function: counterexample_beautificationt::get_minimization_list

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautificationt::get_minimization_list(
  const bv_cbmct &bv_cbmc,
  const symex_target_equationt &equation,
  minimization_listt &minimization_list)
{
  // ignore the ones that are assigned under false guards

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
  {
    if(it->is_assignment() &&
       it->assignment_type==symex_targett::STATE)
    {
      if(!bv_cbmc.prop.l_get(it->guard_literal).is_false())
        if(it->original_lhs_object.type()!=bool_typet())
          minimization_list.insert(it->ssa_lhs);
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

/*******************************************************************\

Function: counterexample_beautificationt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautificationt::operator()(
  bv_cbmct &bv_cbmc,
  const symex_target_equationt &equation,
  const namespacet &ns)
{
  // find failed claim

  failed=get_failed_claim(bv_cbmc, equation);
  
  // lock the failed assertion
  bv_cbmc.prop.l_set_to(failed->cond_literal, false);

  {
    bv_cbmc.status("Beautifying counterexample (guards)");

    // compute weights for guards
    typedef std::map<literalt, unsigned> guard_countt;
    guard_countt guard_count;

    for(symex_target_equationt::SSA_stepst::const_iterator
        it=equation.SSA_steps.begin();
        it!=equation.SSA_steps.end(); it++)
    {
      if(it->is_assignment() &&
         it->assignment_type!=symex_targett::HIDDEN)
      {
        if(!it->guard_literal.is_constant())
          guard_count[it->guard_literal]++;
      }

      // reached failed assertion?
      if(it==failed)
        break;
    }

    // give to propositional minimizer
    prop_minimizet prop_minimize(bv_cbmc);
    prop_minimize.set_message_handler(bv_cbmc.get_message_handler());
    
    for(guard_countt::const_iterator
        it=guard_count.begin();
        it!=guard_count.end();
        it++)
      prop_minimize.objective(it->first, it->second);

    // minimize
    prop_minimize();
  }

  {
    bv_cbmc.status("Beautifying counterexample (values)");

    // get symbols we care about
    minimization_listt minimization_list;
  
    get_minimization_list(bv_cbmc, equation, minimization_list);
  
    // minimize
    bv_minimizet bv_minimize(bv_cbmc);
    bv_minimize.absolute_value=true;
    bv_minimize.set_message_handler(bv_cbmc.get_message_handler());
    bv_minimize(minimization_list);
  }
}
