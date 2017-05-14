/*******************************************************************\

Module: Fault Localization

Author: Peter Schrammel

\*******************************************************************/

#include <util/threeval.h>
#include <util/arith_tools.h>
#include <util/symbol.h>
#include <util/std_expr.h>
#include <util/message.h>
#include <util/time_stopping.h>

#include <solvers/prop/minimize.h>
#include <solvers/prop/literal_expr.h>

#include <goto-symex/build_goto_trace.h>

#include "fault_localization.h"
#include "counterexample_beautification.h"

/*******************************************************************\

Function: fault_localizationt::freeze_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::freeze_guards()
{
  for(const auto &step : bmc.equation.SSA_steps)
  {
    if(!step.guard_literal.is_constant())
      bmc.prop_conv.set_frozen(step.guard_literal);
    if(step.is_assert() &&
       !step.cond_literal.is_constant())
      bmc.prop_conv.set_frozen(step.cond_literal);
  }
}

/*******************************************************************\

Function: fault_localizationt::collect_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::collect_guards(lpointst &lpoints)
{
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=bmc.equation.SSA_steps.begin();
      it!=bmc.equation.SSA_steps.end(); it++)
  {
    if(it->is_assignment() &&
       it->assignment_type==symex_targett::assignment_typet::STATE &&
       !it->ignore)
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
fault_localizationt::get_failed_property()
{
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=bmc.equation.SSA_steps.begin();
      it!=bmc.equation.SSA_steps.end(); it++)
    if(it->is_assert() &&
       bmc.prop_conv.l_get(it->guard_literal).is_true() &&
       bmc.prop_conv.l_get(it->cond_literal).is_false())
      return it;

  assert(false);
  return bmc.equation.SSA_steps.end();
}

/*******************************************************************\

Function: fault_localizationt::check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool fault_localizationt::check(const lpointst &lpoints,
                                const lpoints_valuet &value)
{
  assert(value.size()==lpoints.size());
  bvt assumptions;
  lpoints_valuet::const_iterator v_it=value.begin();
  for(const auto &l : lpoints)
  {
    if(v_it->is_true())
      assumptions.push_back(l.first);
    else if(v_it->is_false())
      assumptions.push_back(!l.first);
    ++v_it;
  }

  // lock the failed assertion
  assumptions.push_back(!failed->cond_literal);

  bmc.prop_conv.set_assumptions(assumptions);

  if(bmc.prop_conv()==decision_proceduret::D_SATISFIABLE)
    return false;

  return true;
}

/*******************************************************************\

Function: fault_localizationt::update_scores

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::update_scores(lpointst &lpoints,
                                        const lpoints_valuet &value)
{
  for(auto &l : lpoints)
  {
    if(bmc.prop_conv.l_get(l.first).is_true())
    {
      l.second.score++;
    }
    else if(bmc.prop_conv.l_get(l.first).is_false() &&
            l.second.score>0)
    {
      l.second.score--;
    }
  }
}

/*******************************************************************\

Function: fault_localizationt::localize_linear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::localize_linear(lpointst &lpoints)
{
  lpoints_valuet v;
  v.resize(lpoints.size());
  for(size_t i=0; i<lpoints.size(); ++i)
    v[i]=tvt(tvt::tv_enumt::TV_UNKNOWN);
  for(size_t i=0; i<v.size(); ++i)
  {
    v[i]=tvt(tvt::tv_enumt::TV_TRUE);
    if(!check(lpoints, v))
      update_scores(lpoints, v);
    v[i]=tvt(tvt::tv_enumt::TV_FALSE);
    if(!check(lpoints, v))
      update_scores(lpoints, v);
    v[i]=tvt(tvt::tv_enumt::TV_UNKNOWN);
  }
}

/*******************************************************************\

Function: fault_localizationt::run

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::run(irep_idt goal_id)
{
  // find failed property
  failed=get_failed_property();
  assert(failed!=bmc.equation.SSA_steps.end());

  if(goal_id==ID_nil)
    goal_id=failed->source.pc->source_location.get_property_id();
  lpointst &lpoints = lpoints_map[goal_id];

  // collect lpoints
  collect_guards(lpoints);

  if(lpoints.empty())
    return;

  status() << "Localizing fault" << eom;

  // pick localization method
  //  if(options.get_option("localize-faults-method")=="TBD")
  localize_linear(lpoints);

  // clear assumptions
  bvt assumptions;
  bmc.prop_conv.set_assumptions(assumptions);
}

/*******************************************************************\

Function: fault_localizationt::report()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::report(irep_idt goal_id)
{
  if(goal_id==ID_nil)
    goal_id=failed->source.pc->source_location.get_property_id();

  lpointst &lpoints = lpoints_map[goal_id];

  if(lpoints.empty())
  {
    status() << "["+id2string(goal_id)+"]: \n"
                   << "   unable to localize fault"
                   << eom;
    return;
  }

  debug() << "Fault localization scores:" << eom;
  lpointt &max=lpoints.begin()->second;
  for(auto &l : lpoints)
  {
    debug() << l.second.target->source_location
            << "\n  score: " << l.second.score << eom;
    if(max.score<l.second.score)
      max=l.second;
  }
  status() << "["+id2string(goal_id)+"]: \n"
                   << "  " << max.target->source_location
                   << eom;
}

/*******************************************************************\

Function: fault_localizationt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::resultt fault_localizationt::operator()()
{
  if(options.get_bool_option("stop-on-fail"))
    return stop_on_fail();
  else
    return bmc_all_propertiest::operator()();
}

/*******************************************************************\

Function: fault_localizationt::run_decision_procedure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt
fault_localizationt::run_decision_procedure(prop_convt &prop_conv)
{
  status() << "Passing problem to "
               << prop_conv.decision_procedure_text() << eom;

  prop_conv.set_message_handler(bmc.get_message_handler());

  // stop the time
  absolute_timet sat_start=current_time();

  bmc.do_conversion();

  freeze_guards();

  status() << "Running " << prop_conv.decision_procedure_text()
               << eom;

  decision_proceduret::resultt dec_result=prop_conv.dec_solve();
  // output runtime

  {
    absolute_timet sat_stop=current_time();
    status() << "Runtime decision procedure: "
             << (sat_stop-sat_start) << "s" << eom;
  }

  return dec_result;
}

/*******************************************************************\

Function: fault_localizationt::stop_on_fail

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

safety_checkert::resultt fault_localizationt::stop_on_fail()
{
  switch(run_decision_procedure(bmc.prop_conv))
  {
  case decision_proceduret::D_UNSATISFIABLE:
    bmc.report_success();
    return safety_checkert::resultt::SAFE;

  case decision_proceduret::D_SATISFIABLE:
    if(options.get_bool_option("trace"))
    {
      if(options.get_bool_option("beautify"))
        counterexample_beautificationt()(
          dynamic_cast<bv_cbmct &>(bmc.prop_conv), bmc.equation, bmc.ns);

      bmc.error_trace();
    }

    // localize faults
    run(ID_nil);
    status() << "\n** Most likely fault location:" << eom;
    report(ID_nil);

    bmc.report_failure();
    return safety_checkert::resultt::UNSAFE;

  default:
    error() << "decision procedure failed" << eom;

    return safety_checkert::resultt::ERROR;
  }
}

/*******************************************************************\

Function: fault_localizationt::goal_covered

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::goal_covered(
  const cover_goalst::goalt &)
{
  for(auto &g : goal_map)
  {
    // failed already?
    if(g.second.status==goalt::statust::FAILURE)
      continue;

    // check whether failed
    for(auto &c : g.second.instances)
    {
      literalt cond=c->cond_literal;

      if(solver.l_get(cond).is_false())
      {
        g.second.status=goalt::statust::FAILURE;
        symex_target_equationt::SSA_stepst::iterator next=c;
        next++; // include the assertion
        build_goto_trace(bmc.equation, next, solver, bmc.ns,
                         g.second.goto_trace);

        // localize faults
        run(g.first);

        break;
      }
    }
  }
}

/*******************************************************************\

Function: fault_localizationt::report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fault_localizationt::report(
  const cover_goalst &cover_goals)
{
  bmc_all_propertiest::report(cover_goals);

  switch(bmc.ui)
  {
  case ui_message_handlert::uit::PLAIN:
    if(cover_goals.number_covered()>0)
    {
      status() << "\n** Most likely fault location:" << eom;
      for(auto &g : goal_map)
      {
        if(g.second.status!=goalt::statust::FAILURE)
          continue;
        report(g.first);
      }
    }
    break;
  case ui_message_handlert::uit::XML_UI:
    break;
  case ui_message_handlert::uit::JSON_UI:
    break;
  }
}
