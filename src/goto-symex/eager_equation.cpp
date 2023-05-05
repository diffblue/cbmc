/*******************************************************************\

Module: Generate equation and solve upon encountering an assertion

Author: Michael Tautschnig

\*******************************************************************/

#include "eager_equation.h"

#if 0

void eager_equationt::assertion(
  const exprt &guard,
  const exprt &cond,
  const std::string &msg,
  const sourcet &source)
{
  symex_target_equationt::assertion(guard, cond, msg, source);

  // from symex_target_equationt::convert(decision_procedure)
  const auto convert_SSA_start = std::chrono::steady_clock::now();

  convert_without_assertions(decision_procedure);
  // TODO now convert all prior assertions into assumptions
  // TODO convert just this assertion
  // DON'T convert_assertions(decision_procedure);

  const auto convert_SSA_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> convert_SSA_runtime =
    std::chrono::duration<double>(convert_SSA_stop - convert_SSA_start);
  log.status() << "Runtime Convert SSA: " << convert_SSA_runtime.count() << "s"
               << messaget::eom;
}

void symex_target_equationt::convert_assumptions(
  decision_proceduret &decision_procedure)
{
  std::size_t step_index = 0;
  for(auto &step : SSA_steps)
  {
    if(step.is_assume())
    {
      if(step.ignore)
        step.cond_handle = true_exprt();
      else
      {
        log.conditional_output(
          log.debug(), [&step](messaget::mstreamt &mstream) {
            step.output(mstream);
            mstream << messaget::eom;
          });

        step.cond_handle = decision_procedure.handle(step.cond_expr);

        with_solver_hardness(
          decision_procedure, hardness_register_ssa(step_index, step));
      }
    }
    ++step_index;
  }
}

void symex_target_equationt::convert_assertions(
  decision_proceduret &decision_procedure,
  bool optimized_for_single_assertions)
{
  // we find out if there is only _one_ assertion,
  // which allows for a simpler formula

  std::size_t number_of_assertions=count_assertions();

  if(number_of_assertions==0)
    return;

  if(number_of_assertions == 1 && optimized_for_single_assertions)
  {
    std::size_t step_index = 0;
    for(auto &step : SSA_steps)
    {
      // hide already converted assertions in the error trace
      if(step.is_assert() && step.converted)
        step.hidden = true;

      if(step.is_assert() && !step.ignore && !step.converted)
      {
        step.converted = true;
        decision_procedure.set_to_false(step.cond_expr);
        step.cond_handle = false_exprt();

        with_solver_hardness(
          decision_procedure, hardness_register_ssa(step_index, step));
        return; // prevent further assumptions!
      }
      else if(step.is_assume())
      {
        decision_procedure.set_to_true(step.cond_expr);

        with_solver_hardness(
          decision_procedure, hardness_register_ssa(step_index, step));
      }
      ++step_index;
    }

    UNREACHABLE; // unreachable
  }

  // We do (NOT a1) OR (NOT a2) ...
  // where the a's are the assertions
  or_exprt::operandst disjuncts;
  disjuncts.reserve(number_of_assertions);

  exprt assumption=true_exprt();

  std::vector<goto_programt::const_targett> involved_steps;

  for(auto &step : SSA_steps)
  {
    // hide already converted assertions in the error trace
    if(step.is_assert() && step.converted)
      step.hidden = true;

    if(step.is_assert() && !step.ignore && !step.converted)
    {
      step.converted = true;

      log.conditional_output(log.debug(), [&step](messaget::mstreamt &mstream) {
        step.output(mstream);
        mstream << messaget::eom;
      });

      implies_exprt implication(
        assumption,
        step.cond_expr);

      // do the conversion
      step.cond_handle = decision_procedure.handle(implication);

      with_solver_hardness(
        decision_procedure,
        [&involved_steps, &step](solver_hardnesst &hardness) {
          involved_steps.push_back(step.source.pc);
        });

      // store disjunct
      disjuncts.push_back(not_exprt(step.cond_handle));
    }
    else if(step.is_assume())
    {
      // the assumptions have been converted before
      // avoid deep nesting of ID_and expressions
      if(assumption.id()==ID_and)
        assumption.copy_to_operands(step.cond_handle);
      else
        assumption = and_exprt(assumption, step.cond_handle);

      with_solver_hardness(
        decision_procedure,
        [&involved_steps, &step](solver_hardnesst &hardness) {
          involved_steps.push_back(step.source.pc);
        });
    }
  }

  const auto assertion_disjunction = disjunction(disjuncts);
  // the below is 'true' if there are no assertions
  decision_procedure.set_to_true(assertion_disjunction);

  with_solver_hardness(
    decision_procedure,
    [&assertion_disjunction, &involved_steps](solver_hardnesst &hardness) {
      hardness.register_assertion_ssas(assertion_disjunction, involved_steps);
    });
}

#endif
