/*******************************************************************\

Module: Property Decider for Goto-Symex

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Property Decider for Goto-Symex

#include "goto_symex_property_decider.h"

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
  decision_procedure = &solver->decision_procedure_incremental();
}

exprt goto_symex_property_decidert::goalt::as_expr() const
{
  exprt::operandst conjuncts;
  conjuncts.reserve(instances.size());
  for(const auto &inst : instances)
    conjuncts.push_back(literal_exprt(inst->cond_literal));
  return conjunction(conjuncts);
}

void goto_symex_property_decidert::
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

void goto_symex_property_decidert::convert_goals()
{
  for(auto &goal_pair : goal_map)
  {
    // Our goal is to falsify a property, i.e., we will
    // add the negation of the property as goal.
    goal_pair.second.condition =
      !decision_procedure->convert(goal_pair.second.as_expr());
  }
}

void goto_symex_property_decidert::freeze_goal_variables()
{
  for(const auto &goal_pair : goal_map)
  {
    if(!goal_pair.second.condition.is_constant())
      decision_procedure->set_frozen(goal_pair.second.condition);
  }
}

void goto_symex_property_decidert::add_constraint_from_goals(
  std::function<bool(const irep_idt &)> select_property)
{
  exprt::operandst disjuncts;

  for(const auto &goal_pair : goal_map)
  {
    if(
      select_property(goal_pair.first) &&
      !goal_pair.second.condition.is_false())
    {
      disjuncts.push_back(literal_exprt(goal_pair.second.condition));
    }
  }

  // this is 'false' if there are no disjuncts
  decision_procedure->set_to_true(disjunction(disjuncts));
}

decision_proceduret::resultt goto_symex_property_decidert::solve()
{
  return (*decision_procedure)();
}

decision_procedure_incrementalt &
goto_symex_property_decidert::get_solver() const
{
  return *decision_procedure;
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
        decision_procedure->l_get(goal_pair.second.condition).is_true() &&
        status != property_statust::FAIL)
      {
        status |= property_statust::FAIL;
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
