/*******************************************************************\

Module: Fault Localization

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Fault Localization

#include "fault_localization.h"

#include <chrono>

#include <util/arith_tools.h>
#include <util/message.h>
#include <util/std_expr.h>
#include <util/symbol.h>
#include <util/threeval.h>
#include <util/xml_irep.h>

#include <solvers/prop/minimize.h>
#include <solvers/prop/literal_expr.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>

#include <goto-checker/bmc_util.h>

#include "counterexample_beautification.h"

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

  UNREACHABLE;
  return bmc.equation.SSA_steps.end();
}

bool fault_localizationt::check(const lpointst &lpoints,
                                const lpoints_valuet &value)
{
  PRECONDITION(value.size() == lpoints.size());
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

  if(bmc.prop_conv()==decision_proceduret::resultt::D_SATISFIABLE)
    return false;

  return true;
}

void fault_localizationt::update_scores(lpointst &lpoints)
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
      update_scores(lpoints);
    v[i]=tvt(tvt::tv_enumt::TV_FALSE);
    if(!check(lpoints, v))
      update_scores(lpoints);
    v[i]=tvt(tvt::tv_enumt::TV_UNKNOWN);
  }
}

void fault_localizationt::run(irep_idt goal_id)
{
  // find failed property
  failed=get_failed_property();
  PRECONDITION(failed != bmc.equation.SSA_steps.end());

  if(goal_id==ID_nil)
    goal_id=failed->source.pc->source_location.get_property_id();
  lpointst &lpoints=lpoints_map[goal_id];

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

void fault_localizationt::report(irep_idt goal_id)
{
  if(goal_id==ID_nil)
    goal_id=failed->source.pc->source_location.get_property_id();

  lpointst &lpoints=lpoints_map[goal_id];

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

xmlt fault_localizationt::report_xml(irep_idt goal_id)
{
  xmlt xml_diagnosis("diagnosis");
  xml_diagnosis.new_element("method").data="linear fault localization";

  if(goal_id==ID_nil)
    goal_id=failed->source.pc->source_location.get_property_id();

  xml_diagnosis.set_attribute("property", id2string(goal_id));

  const lpointst &lpoints=lpoints_map[goal_id];

  if(lpoints.empty())
  {
    xml_diagnosis.new_element("result").data="unable to localize fault";
    return xml_diagnosis;
  }

  debug() << "Fault localization scores:" << eom;
  const lpointt *max=&lpoints.begin()->second;
  for(const auto &pair : lpoints)
  {
    const auto &value=pair.second;
    debug() << value.target->source_location
            << "\n  score: " << value.score << eom;
    if(max->score<value.score)
      max=&value;
  }

  xmlt xml_location=xml(max->target->source_location);
  xml_diagnosis.new_element("result").new_element().swap(xml_location);

  return xml_diagnosis;
}

safety_checkert::resultt fault_localizationt::operator()()
{
  if(options.get_bool_option("stop-on-fail"))
    return stop_on_fail();
  else
    return bmc_all_propertiest::operator()();
}

decision_proceduret::resultt
fault_localizationt::run_decision_procedure(prop_convt &prop_conv)
{
  status() << "Passing problem to "
               << prop_conv.decision_procedure_text() << eom;

  prop_conv.set_message_handler(bmc.get_message_handler());

  auto solver_start=std::chrono::steady_clock::now();

  convert_symex_target_equation(
    bmc.equation, bmc.prop_conv, get_message_handler());
  bmc.freeze_program_variables();

  freeze_guards();

  status() << "Running " << prop_conv.decision_procedure_text()
               << eom;

  decision_proceduret::resultt dec_result=prop_conv.dec_solve();
  // output runtime

  {
    auto solver_stop=std::chrono::steady_clock::now();
    status() << "Runtime decision procedure: "
             << std::chrono::duration<double>(solver_stop-solver_start).count()
             << "s" << eom;
  }

  return dec_result;
}

safety_checkert::resultt fault_localizationt::stop_on_fail()
{
  switch(run_decision_procedure(bmc.prop_conv))
  {
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    report_success(bmc.ui_message_handler);
    return safety_checkert::resultt::SAFE;

  case decision_proceduret::resultt::D_SATISFIABLE:
    if(options.get_bool_option("trace"))
    {
      if(options.get_bool_option("beautify"))
        counterexample_beautificationt()(
          dynamic_cast<boolbvt &>(bmc.prop_conv), bmc.equation);

      build_error_trace(
        bmc.error_trace,
        bmc.ns,
        bmc.equation,
        bmc.prop_conv,
        bmc.ui_message_handler);
      output_error_trace(
        bmc.error_trace, bmc.ns, bmc.trace_options(), bmc.ui_message_handler);
    }

    // localize faults
    run(ID_nil);

    switch(bmc.ui_message_handler.get_ui())
    {
    case ui_message_handlert::uit::PLAIN:
    {
      status() << "\n** Most likely fault location:" << eom;
      report(ID_nil);
      break;
    }
    case ui_message_handlert::uit::XML_UI:
    {
      xmlt dest("fault-localization", {}, {report_xml(ID_nil)});
      status() << dest;
      break;
    }
    case ui_message_handlert::uit::JSON_UI:
      // not implemented
      break;
    }

    report_failure(bmc.ui_message_handler);
    return safety_checkert::resultt::UNSAFE;

  default:
    error() << "decision procedure failed" << eom;

    return safety_checkert::resultt::ERROR;
  }

  UNREACHABLE;
}

void fault_localizationt::goal_covered(
  const cover_goalst::goalt &)
{
  for(auto &goal_pair : goal_map)
  {
    // failed already?
    if(goal_pair.second.status==goalt::statust::FAILURE)
      continue;

    // check whether failed
    for(auto &inst : goal_pair.second.instances)
    {
      literalt cond=inst->cond_literal;

      if(solver.l_get(cond).is_false())
      {
        goal_pair.second.status=goalt::statust::FAILURE;
        build_goto_trace(
          bmc.equation, inst, solver, bmc.ns, goal_pair.second.goto_trace);

        // localize faults
        run(goal_pair.first);

        break;
      }
    }
  }
}

void fault_localizationt::report(
  const cover_goalst &cover_goals)
{
  bmc_all_propertiest::report(cover_goals);

  switch(bmc.ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    if(cover_goals.number_covered()>0)
    {
      status() << "\n** Most likely fault location:" << eom;
      for(auto &goal_pair : goal_map)
      {
        if(goal_pair.second.status!=goalt::statust::FAILURE)
          continue;
        report(goal_pair.first);
      }
    }
    break;
  case ui_message_handlert::uit::XML_UI:
    {
      xmlt dest("fault-localization");
      for(auto &goal_pair : goal_map)
      {
        if(goal_pair.second.status!=goalt::statust::FAILURE)
          continue;
        xmlt xml_diagnosis=report_xml(goal_pair.first);
        dest.new_element().swap(xml_diagnosis);
      }
      status() << dest;
    }
    break;
  case ui_message_handlert::uit::JSON_UI:
    // not implemented
    break;
  }
}
