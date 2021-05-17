// Author: Diffblue Ltd.

#include "smt2_incremental_decision_procedure.h"

#include <util/expr.h>

smt2_incremental_decision_proceduret::smt2_incremental_decision_proceduret(
  std::string solver_command)
  : solver_command{std::move(solver_command)}
{
}

exprt smt2_incremental_decision_proceduret::handle(const exprt &expr)
{
  UNIMPLEMENTED;
  return exprt();
}

exprt smt2_incremental_decision_proceduret::get(const exprt &expr) const
{
  UNIMPLEMENTED;
  return exprt();
}

void smt2_incremental_decision_proceduret::print_assignment(
  std::ostream &out) const
{
  UNIMPLEMENTED;
}

std::string
smt2_incremental_decision_proceduret::decision_procedure_text() const
{
  return "incremental SMT2 solving via \"" + solver_command + "\"";
}

std::size_t
smt2_incremental_decision_proceduret::get_number_of_solver_calls() const
{
  UNIMPLEMENTED;
  return 0;
}

void smt2_incremental_decision_proceduret::set_to(const exprt &expr, bool value)
{
  UNIMPLEMENTED;
}

void smt2_incremental_decision_proceduret::push(
  const std::vector<exprt> &assumptions)
{
  UNIMPLEMENTED;
}

void smt2_incremental_decision_proceduret::push()
{
  UNIMPLEMENTED;
}

void smt2_incremental_decision_proceduret::pop()
{
  UNIMPLEMENTED;
}

decision_proceduret::resultt smt2_incremental_decision_proceduret::dec_solve()
{
  UNIMPLEMENTED;
  return decision_proceduret::resultt::D_SATISFIABLE;
}
