/*******************************************************************\

Module: Fault Localization for Goto Symex

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Fault Localization for Goto Symex

#include "goto_symex_fault_localizer.h"

goto_symex_fault_localizert::goto_symex_fault_localizert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  const symex_target_equationt &equation,
  stack_decision_proceduret &solver)
  : options(options),
    ui_message_handler(ui_message_handler),
    equation(equation),
    solver(solver)
{
}

fault_location_infot goto_symex_fault_localizert::
operator()(const irep_idt &failed_property_id)
{
  fault_location_infot fault_location;
  localization_pointst localization_points;
  const auto &failed_step =
    collect_guards(failed_property_id, localization_points, fault_location);

  if(!localization_points.empty())
  {
    messaget log(ui_message_handler);
    log.status() << "Localizing fault" << messaget::eom;

    // pick localization method
    //  if(options.get_option("localize-faults-method")=="TBD")
    localize_linear(failed_step, localization_points);
  }

  return fault_location;
}

const SSA_stept &goto_symex_fault_localizert::collect_guards(
  const irep_idt &failed_property_id,
  localization_pointst &localization_points,
  fault_location_infot &fault_location)
{
  for(const auto &step : equation.SSA_steps)
  {
    if(
      step.is_assignment() &&
      step.assignment_type == symex_targett::assignment_typet::STATE &&
      !step.ignore)
    {
      exprt l = solver.handle(step.guard_handle);
      if(!l.is_constant())
      {
        auto emplace_result = fault_location.scores.emplace(step.source.pc, 0);
        localization_points.emplace(l, emplace_result.first);
      }
    }

    // reached failed assertion?
    if(step.is_assert() && step.get_property_id() == failed_property_id)
      return step;
  }
  UNREACHABLE;
}

bool goto_symex_fault_localizert::check(
  const SSA_stept &failed_step,
  const localization_pointst &localization_points,
  const localization_points_valuet &value)
{
  PRECONDITION(value.size() == localization_points.size());
  std::vector<exprt> assumptions;
  localization_points_valuet::const_iterator v_it = value.begin();
  for(const auto &l : localization_points)
  {
    if(v_it->is_true())
      assumptions.push_back(l.first);
    else if(v_it->is_false())
      assumptions.push_back(solver.handle(not_exprt(l.first)));
    ++v_it;
  }

  // lock the failed assertion
  assumptions.push_back(solver.handle(not_exprt(failed_step.cond_handle)));

  solver.push(assumptions);

  return solver() != decision_proceduret::resultt::D_SATISFIABLE;
}

void goto_symex_fault_localizert::update_scores(
  const localization_pointst &localization_points)
{
  for(auto &l : localization_points)
  {
    auto &score = l.second->second;
    if(solver.get(l.first).is_true())
    {
      score++;
    }
    else if(solver.get(l.first).is_false() && score > 0)
    {
      score--;
    }
  }
}

void goto_symex_fault_localizert::localize_linear(
  const SSA_stept &failed_step,
  const localization_pointst &localization_points)
{
  localization_points_valuet v(localization_points.size(), tvt::unknown());

  for(std::size_t i = 0; i < v.size(); ++i)
  {
    v[i] = tvt(tvt::tv_enumt::TV_TRUE);
    if(!check(failed_step, localization_points, v))
      update_scores(localization_points);

    v[i] = tvt(tvt::tv_enumt::TV_FALSE);
    if(!check(failed_step, localization_points, v))
      update_scores(localization_points);

    v[i] = tvt::unknown();
  }

  // clear assumptions
  solver.pop();
}
