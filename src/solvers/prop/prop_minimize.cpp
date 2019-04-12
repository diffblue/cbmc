/*******************************************************************\

Module: Minimize some target function incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Minimize some target function incrementally

#include "prop_minimize.h"

#include <util/std_expr.h>

prop_minimizet::prop_minimizet(
  decision_proceduret &_decision_procedure,
  message_handlert &message_handler)
  : decision_procedure(_decision_procedure), log(message_handler)
{
}

/// Add an objective
void prop_minimizet::objective(exprt condition, const weightt weight)
{
  if(weight > 0)
  {
    objectives[weight].emplace_back(std::move(condition));
    _number_objectives++;
  }
  else if(weight < 0)
  {
    objectives[-weight].emplace_back(not_exprt(std::move(condition)));
    _number_objectives++;
  }
}

/// Fix objectives that are satisfied
void prop_minimizet::fix_objectives()
{
  std::vector<objectivet> &entry = current->second;
  bool found = false;

  for(auto &objective : entry)
  {
    if(!objective.fixed && decision_procedure.get(objective.condition).is_false())
    {
      _number_satisfied++;
      _value += current->first;
      decision_procedure.set_to(objective.condition, false); // fix it
      objective.fixed = true;
      found = true;
    }
  }

  POSTCONDITION(found);
}

/// Build constraints that require us to improve on at least one goal, greedily.
exprt prop_minimizet::constraint()
{
  std::vector<objectivet> &entry = current->second;

  exprt::operandst disjuncts;

  for(const auto &objective : entry)
  {
    if(!objective.fixed)
      disjuncts.push_back(not_exprt(objective.condition));
  }

  // This returns false if the clause is empty,
  // i.e., no further improvement possible.
  return disjunction(disjuncts);
}

/// Try to cover all objectives
void prop_minimizet::operator()()
{
  // we need to use assumptions
  PRECONDITION(decision_procedure.has_set_assumptions());

  _iterations = 0;
  _number_satisfied = 0;
  _value = 0;
  bool last_was_SAT = false;

  // go from high weights to low ones
  for(current = objectives.rbegin(); current != objectives.rend(); current++)
  {
    log.status() << "weight " << current->first << messaget::eom;

    decision_proceduret::resultt dec_result;
    do
    {
      // We want to improve on one of the objectives, please!
      auto c = constraint();

      if(c.is_false())
        dec_result = decision_proceduret::resultt::D_UNSATISFIABLE;
      else
      {
        _iterations++;

        exprt::operandst assumptions;
        assumptions.push_back(c);
        decision_procedure.set_assumptions(assumptions);
        dec_result = decision_procedure();

        switch(dec_result)
        {
        case decision_proceduret::resultt::D_UNSATISFIABLE:
          last_was_SAT = false;
          break;

        case decision_proceduret::resultt::D_SATISFIABLE:
          last_was_SAT = true;
          fix_objectives(); // fix the ones we got
          break;

        default:
          log.error() << "decision procedure failed" << messaget::eom;
          last_was_SAT = false;
          return;
        }
      }
    } while(dec_result != decision_proceduret::resultt::D_UNSATISFIABLE);
  }

  if(!last_was_SAT)
  {
    // We don't have a satisfying assignment to work with.
    // Run solver again to get one.

    // no assumptions
    decision_procedure.set_assumptions({});
    (void)decision_procedure();
  }
}
