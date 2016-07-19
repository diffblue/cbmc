/*******************************************************************\

Module: Fault Localization

Author: Peter Schrammel

\*******************************************************************/

#include <util/threeval.h>
#include <util/expr_util.h>
#include <util/arith_tools.h>
#include <util/symbol.h>
#include <util/std_expr.h>
#include <util/message.h>

#include <solvers/prop/minimize.h>
#include <solvers/prop/literal_expr.h>

#include "fault_localization.h"

/*******************************************************************\

Function: fault_localizationt::collect_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::collect_guards(
  const symex_target_equationt &equation)
{
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
  {
    if(it->is_assignment() &&
       it->assignment_type==symex_targett::STATE)
    {
      if(!it->guard_literal.is_constant())
      {
        lpoints[it->guard_literal].target=it->source.pc;
        lpoints[it->guard_literal].score=0;
      }
    }

    // reached failed assertion?
    if(it==failed)
      break;
  }
}

/*******************************************************************\

Function: fault_localizationt::get_failed_property

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symex_target_equationt::SSA_stepst::const_iterator
fault_localizationt::get_failed_property(
  const prop_convt &prop_conv,
  const symex_target_equationt &equation)
{
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
    if(it->is_assert() &&
       prop_conv.l_get(it->guard_literal).is_true() &&
       prop_conv.l_get(it->cond_literal).is_false())
      return it;
  
  assert(false);
  return equation.SSA_steps.end();
}

/*******************************************************************\

Function: fault_localizationt::check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool fault_localizationt::check(
    prop_convt &prop_conv,
    const lpoints_valuet& value)
{
  assert(value.size()==lpoints.size());
  bvt assumptions;
  lpointst::const_iterator l_it=lpoints.begin();
  lpoints_valuet::const_iterator v_it=value.begin();
  for(; l_it!=lpoints.end(); 
      ++l_it, ++v_it)
  {
    if(v_it->is_true())
      assumptions.push_back(l_it->first);
    else if(v_it->is_false())
      assumptions.push_back(!l_it->first);
  }
  prop_conv.set_assumptions(assumptions);

  if(prop_conv()==decision_proceduret::D_SATISFIABLE)
    return false;

  return true;
}

/*******************************************************************\

Function: fault_localizationt::update_scores

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::update_scores(
    const prop_convt &prop_conv,
    const lpoints_valuet& value)
{
  for(lpointst::iterator l_it=lpoints.begin();
      l_it!=lpoints.end();
      ++l_it)
  {
    if(prop_conv.l_get(l_it->first).is_true())
      l_it->second.score++;
    else if(prop_conv.l_get(l_it->first).is_false() &&
            l_it->second.score>0)
      l_it->second.score--;
  }
}

/*******************************************************************\

Function: fault_localizationt::localize_linear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::localize_linear(
    prop_convt &prop_conv)
{
  lpoints_valuet v;
  for(lpointst::const_iterator l_it=lpoints.begin();
      l_it!=lpoints.end();
      ++l_it)
    v.push_back(tvt(tvt::tv_enumt::TV_UNKNOWN));
  for(size_t i=0; i<v.size(); ++i)
  {
    v[i]=tvt(tvt::tv_enumt::TV_TRUE);
    if(!check(prop_conv, v))
      update_scores(prop_conv, v);
    v[i]=tvt(tvt::tv_enumt::TV_FALSE);
    if(!check(prop_conv, v))
      update_scores(prop_conv, v);
    v[i]=tvt(tvt::tv_enumt::TV_UNKNOWN);
  }
}

/*******************************************************************\

Function: fault_localizationt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::operator()(
  bv_cbmct &bv_cbmc,
  const symex_target_equationt &equation,
  const namespacet &ns)
{
  // find failed property
  failed=get_failed_property(bv_cbmc, equation);

  if(failed==equation.SSA_steps.end())
    return;
  
  // lock the failed assertion
  bv_cbmc.set_to(literal_exprt(failed->cond_literal), false);

  // collect lpoints
  collect_guards(equation);

  if(lpoints.empty())
    return;

  bv_cbmc.status() << "Localizing fault"
                   << messaget::eom;

  // pick localization method
  //  if(options.get_option("localize-faults-method")=="TBD")
  localize_linear(bv_cbmc);

  // print results
  report(bv_cbmc);
}

/*******************************************************************\

Function: fault_localizationt::report()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::report(
  bv_cbmct &bv_cbmc)

{
  assert(!lpoints.empty());
  lpointst::const_iterator max=lpoints.begin();
  bv_cbmc.debug() << "Fault localization scores:" << messaget::eom;
  for(lpointst::const_iterator l_it=lpoints.begin();
      l_it!=lpoints.end(); 
      ++l_it)
  {
    bv_cbmc.debug() << l_it->second.target->source_location 
            << "\n  score: " << l_it->second.score << messaget::eom;
    if(max->second.score<l_it->second.score)
      max=l_it;
  }
  bv_cbmc.status() << "Most likely fault location: \n"
                   << "  " << max->second.target->source_location
                   << messaget::eom;
}
