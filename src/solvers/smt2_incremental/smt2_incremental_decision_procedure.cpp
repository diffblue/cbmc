// Author: Diffblue Ltd.

#include "smt2_incremental_decision_procedure.h"

#include <util/expr.h>

smt2_incremental_decision_proceduret::smt2_incremental_decision_proceduret(
  std::string solver_command)
  : solver_command{std::move(solver_command)}, number_of_solver_calls{0}
{
}

exprt smt2_incremental_decision_proceduret::handle(const exprt &expr)
{
  return expr;
}

exprt smt2_incremental_decision_proceduret::get(const exprt &expr) const
{
  UNIMPLEMENTED_FEATURE("`get` of:\n  " + expr.pretty(2, 0));
}

void smt2_incremental_decision_proceduret::print_assignment(
  std::ostream &out) const
{
  UNIMPLEMENTED_FEATURE("printing of assignments.");
}

std::string
smt2_incremental_decision_proceduret::decision_procedure_text() const
{
  return "incremental SMT2 solving via \"" + solver_command + "\"";
}

std::size_t
smt2_incremental_decision_proceduret::get_number_of_solver_calls() const
{
  return number_of_solver_calls;
}

void smt2_incremental_decision_proceduret::set_to(const exprt &expr, bool value)
{
  UNIMPLEMENTED_FEATURE(
    "`set_to` (" + std::string{value ? "true" : "false"} + "):\n  " +
    expr.pretty(2, 0));
}

void smt2_incremental_decision_proceduret::push(
  const std::vector<exprt> &assumptions)
{
  for(const auto &assumption : assumptions)
  {
    UNIMPLEMENTED_FEATURE(
      "pushing of assumption:\n  " + assumption.pretty(2, 0));
  }
  UNIMPLEMENTED_FEATURE("`push` of empty assumptions.");
}

void smt2_incremental_decision_proceduret::push()
{
  UNIMPLEMENTED_FEATURE("`push`.");
}

void smt2_incremental_decision_proceduret::pop()
{
  UNIMPLEMENTED_FEATURE("`pop`.");
}

decision_proceduret::resultt smt2_incremental_decision_proceduret::dec_solve()
{
  ++number_of_solver_calls;
  UNIMPLEMENTED_FEATURE("solving.");
}
