/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#include "multi_path_symex_checker.h"

#include <chrono>

#include "bmc_util.h"
#include "counterexample_beautification.h"

multi_path_symex_checkert::multi_path_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : multi_path_symex_only_checkert(options, ui_message_handler, goto_model),
    equation_generated(false)
{
  solver_factoryt solvers(
    options,
    ns,
    ui_message_handler,
    ui_message_handler.get_ui() == ui_message_handlert::uit::XML_UI);
  solver = solvers.get_solver();
  solver->prop_conv().set_message_handler(ui_message_handler);
}

incremental_goto_checkert::resultt multi_path_symex_checkert::
operator()(propertiest &properties)
{
  resultt result(resultt::progresst::DONE);

  // When the equation has been generated, we know all the properties.
  // Have we got anything to check? Otherwise we return DONE.
  if(equation_generated && !has_properties_to_check(properties))
    return result;

  prop_convt &prop_conv = solver->prop_conv();
  std::chrono::duration<double> solver_runtime(0);

  // we haven't got an equation yet
  if(!equation_generated)
  {
    perform_symex();
    output_coverage_report();
    // This might add new properties such as unwinding assertions, for instance.
    update_properties_status_from_symex_target_equation(
      properties, result.updated_properties, equation);
    // Since we will not symex any further we can decide the status
    // of all properties that do not occur in the equation now.
    // The current behavior is PASS.
    update_status_of_not_checked_properties(
      properties, result.updated_properties);

    // Have we got anything to check? Otherwise we return DONE.
    if(!has_properties_to_check(properties))
      return result;

    log.status() << "Passing problem to " << prop_conv.decision_procedure_text()
                 << messaget::eom;

    const auto solver_start = std::chrono::steady_clock::now();

    convert_symex_target_equation(equation, prop_conv, ui_message_handler);
    update_properties_goals_from_symex_target_equation(properties);
    convert_goals();
    freeze_goal_variables();

    const auto solver_stop = std::chrono::steady_clock::now();
    solver_runtime += std::chrono::duration<double>(solver_stop - solver_start);

    log.status() << "Running " << prop_conv.decision_procedure_text()
                 << messaget::eom;
    equation_generated = true;
  }

  const auto solver_start = std::chrono::steady_clock::now();

  add_constraint_from_goals(properties);

  decision_proceduret::resultt dec_result = prop_conv.dec_solve();

  update_properties_status_from_goals(
    properties, result.updated_properties, dec_result);

  const auto solver_stop = std::chrono::steady_clock::now();
  solver_runtime += std::chrono::duration<double>(solver_stop - solver_start);
  log.status() << "Runtime decision procedure: " << solver_runtime.count()
               << "s" << messaget::eom;

  result.progress = dec_result == decision_proceduret::resultt::D_SATISFIABLE
                      ? resultt::progresst::FOUND_FAIL
                      : resultt::progresst::DONE;
  return result;
}

goto_tracet multi_path_symex_checkert::build_trace() const
{
  if(options.get_bool_option("beautify"))
  {
    counterexample_beautificationt()(
      dynamic_cast<boolbvt &>(solver->prop_conv()), equation);
  }
  goto_tracet goto_trace;
  ::build_error_trace(
    goto_trace, ns, equation, solver->prop_conv(), ui_message_handler);
  return goto_trace;
}

const namespacet &multi_path_symex_checkert::get_namespace() const
{
  return ns;
}

void multi_path_symex_checkert::output_proof()
{
  output_graphml(equation, ns, options);
}

void multi_path_symex_checkert::output_error_witness(
  const goto_tracet &error_trace)
{
  output_graphml(error_trace, ns, options);
}

exprt multi_path_symex_checkert::goalt::as_expr() const
{
  std::vector<exprt> tmp;
  tmp.reserve(instances.size());
  for(const auto &inst : instances)
    tmp.push_back(literal_exprt(inst->cond_literal));
  return conjunction(tmp);
}

void multi_path_symex_checkert::
  update_properties_goals_from_symex_target_equation(propertiest &properties)
{
  for(symex_target_equationt::SSA_stepst::iterator it =
        equation.SSA_steps.begin();
      it != equation.SSA_steps.end();
      ++it)
  {
    if(it->is_assert())
    {
      irep_idt property_id = it->get_property_id();
      CHECK_RETURN(!property_id.empty());

      // consider goal instance if it is in the given properties
      auto property_pair_it = properties.find(property_id);
      if(
        property_pair_it != properties.end() &&
        is_property_to_check(property_pair_it->second.status))
      {
        // it's going to be checked, but we don't know the status yet
        property_pair_it->second.status |= property_statust::UNKNOWN;
        goal_map[property_id].instances.push_back(it);
      }
    }
  }
}

void multi_path_symex_checkert::convert_goals()
{
  for(auto &goal_pair : goal_map)
  {
    // Our goal is to falsify a property, i.e., we will
    // add the negation of the property as goal.
    goal_pair.second.condition =
      !solver->prop_conv().convert(goal_pair.second.as_expr());
  }
}

void multi_path_symex_checkert::freeze_goal_variables()
{
  for(const auto &goal_pair : goal_map)
  {
    if(!goal_pair.second.condition.is_constant())
      solver->prop_conv().set_frozen(goal_pair.second.condition);
  }
}

void multi_path_symex_checkert::add_constraint_from_goals(
  const propertiest &properties)
{
  exprt::operandst disjuncts;

  // cover at least one unknown goal

  for(const auto &goal_pair : goal_map)
  {
    if(
      is_property_to_check(properties.at(goal_pair.first).status) &&
      !goal_pair.second.condition.is_false())
    {
      disjuncts.push_back(literal_exprt(goal_pair.second.condition));
    }
  }

  // this is 'false' if there are no disjuncts
  solver->prop_conv().set_to_true(disjunction(disjuncts));
}

void multi_path_symex_checkert::update_properties_status_from_goals(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties,
  decision_proceduret::resultt dec_result)
{
  switch(dec_result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    for(auto &goal_pair : goal_map)
    {
      if(solver->prop_conv().l_get(goal_pair.second.condition).is_true())
      {
        properties.at(goal_pair.first).status |= property_statust::FAIL;
        updated_properties.insert(goal_pair.first);
      }
    }
    break;
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    for(auto &property_pair : properties)
    {
      if(property_pair.second.status == property_statust::UNKNOWN)
      {
        property_pair.second.status |= property_statust::PASS;
        updated_properties.insert(property_pair.first);
      }
    }
    break;
  case decision_proceduret::resultt::D_ERROR:
    for(auto &property_pair : properties)
    {
      if(property_pair.second.status == property_statust::UNKNOWN)
      {
        property_pair.second.status |= property_statust::ERROR;
        updated_properties.insert(property_pair.first);
      }
    }
    break;
  }
}
