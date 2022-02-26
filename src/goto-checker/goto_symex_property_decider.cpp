/*******************************************************************\

Module: Property Decider for Goto-Symex

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Property Decider for Goto-Symex

#include "goto_symex_property_decider.h"

#include <util/expr_util.h>
#include <util/ui_message.h>

#include <solvers/prop/prop.h>

goto_symex_property_decidert::goto_symex_property_decidert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  symex_target_equationt &equation,
  const namespacet &ns)
  : options(options), ui_message_handler(ui_message_handler), equation(equation)
{
  solver_factoryt solvers(
    options,
    ns,
    ui_message_handler,
    ui_message_handler.get_ui() == ui_message_handlert::uit::XML_UI);
  solver = solvers.get_solver();

  // TODO: make this configurable
  cover_goals = true;
}

exprt goto_symex_property_decidert::goalt::build_condition() const
{
  exprt::operandst conjuncts;
  conjuncts.reserve(instances.size());
  for(const auto &inst : instances)
    conjuncts.push_back(inst->cond_handle);

  // Our goal is to falsify a property, i.e., we will
  // add the negation of the property as goal.
  return boolean_negate(conjunction(conjuncts));
}

exprt goto_symex_property_decidert::goalt::build_path_condition() const
{
  exprt::operandst disjuncts;
  disjuncts.reserve(instances.size());
  for(const auto &inst : instances)
    disjuncts.push_back(inst->guard_handle);
  return disjunction(disjuncts);
}

void goto_symex_property_decidert::
  update_properties_goals_from_symex_target_equation(propertiest &properties)
{
  goal_map.clear();

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

void goto_symex_property_decidert::convert_goals()
{
  for(auto &goal_pair : goal_map)
  {
    goal_pair.second.condition =
      solver->decision_procedure().handle(goal_pair.second.build_condition());
    if(cover_goals)
    {
      goal_pair.second.path_condition = solver->decision_procedure().handle(
        goal_pair.second.build_path_condition());
    }
  }
}

void goto_symex_property_decidert::add_constraint_from_goals(
  std::function<bool(const irep_idt &)> select_property,
  const propertiest &properties)
{
  exprt::operandst disjuncts;

  for(const auto &goal_pair : goal_map)
  {
    if(
      select_property(goal_pair.first) &&
      !goal_pair.second.condition.is_false())
    {
      disjuncts.push_back(goal_pair.second.condition);
      if(cover_goals)
      {
        auto &status = properties.at(goal_pair.first).status;
        if(status == property_statust::UNKNOWN)
          disjuncts.push_back(goal_pair.second.path_condition);
      }
    }
  }

  // this is 'false' if there are no disjuncts
  solver->decision_procedure().set_to_true(disjunction(disjuncts));
}

decision_proceduret::resultt goto_symex_property_decidert::solve()
{
  return solver->decision_procedure()();
}

decision_proceduret &
goto_symex_property_decidert::get_decision_procedure() const
{
  return solver->decision_procedure();
}

stack_decision_proceduret &
goto_symex_property_decidert::get_stack_decision_procedure() const
{
  return solver->stack_decision_procedure();
}

symex_target_equationt &goto_symex_property_decidert::get_equation() const
{
  return equation;
}

void goto_symex_property_decidert::update_properties_status_from_goals(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties,
  decision_proceduret::resultt dec_result,
  bool set_pass) const
{
  switch(dec_result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    for(auto &goal_pair : goal_map)
    {
      auto &status = properties.at(goal_pair.first).status;
      if(
        solver->decision_procedure()
          .get(goal_pair.second.condition)
          .is_true() &&
        status != property_statust::FAIL)
      {
        status |= property_statust::FAIL;
        updated_properties.insert(goal_pair.first);
      }
      else if(
        cover_goals && status == property_statust::UNKNOWN &&
        solver->decision_procedure()
          .get(goal_pair.second.path_condition)
          .is_true())
      {
        status = property_statust::NOT_CHECKED;
        updated_properties.insert(goal_pair.first);
      }
    }
    break;
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    if(!set_pass)
      break;

    for(auto &property_pair : properties)
    {
      if(property_pair.second.status == property_statust::UNKNOWN)
      {
        if(cover_goals)
          property_pair.second.status |= property_statust::NOT_REACHABLE;
        else
          property_pair.second.status |= property_statust::PASS;
        updated_properties.insert(property_pair.first);
      }
      else if(property_pair.second.status == property_statust::NOT_CHECKED)
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
