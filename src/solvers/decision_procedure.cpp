/*******************************************************************\

Module: Decision Procedure Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Decision Procedure Interface

#include "decision_procedure.h"

#include <util/std_expr.h>

decision_proceduret::~decision_proceduret()
{
}

decision_proceduret::resultt decision_proceduret::operator()()
{
  auto result = dec_solve(nil_exprt());
  latest_result = result;
  return result;
}

decision_proceduret::resultt
decision_proceduret::operator()(const exprt &assumption)
{
  auto result = dec_solve(assumption);
  latest_result = result;
  return result;
}

void decision_proceduret::set_to_true(const exprt &expr)
{
  latest_result = resultt::D_ERROR;
  set_to(expr, true);
}

void decision_proceduret::set_to_false(const exprt &expr)
{
  latest_result = resultt::D_ERROR;
  set_to(expr, false);
}
