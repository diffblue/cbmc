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
  // dec_solve() may throw (e.g., on solver interruption). Ensure
  // latest_result is set to D_ERROR in that case so that get_status() does
  // not report a stale satisfiability result.
  try
  {
    auto result = dec_solve(nil_exprt());
    latest_result = result;
    return result;
  }
  catch(...)
  {
    latest_result = resultt::D_ERROR;
    throw;
  }
}

decision_proceduret::resultt
decision_proceduret::operator()(const exprt &assumption)
{
  try
  {
    auto result = dec_solve(assumption);
    latest_result = result;
    return result;
  }
  catch(...)
  {
    latest_result = resultt::D_ERROR;
    throw;
  }
}

void decision_proceduret::set_to_true(const exprt &expr)
{
  set_to(expr, true);
}

void decision_proceduret::set_to_false(const exprt &expr)
{
  set_to(expr, false);
}

exprt decision_proceduret::handle(const exprt &expr)
{
  latest_result = resultt::D_ERROR;
  return do_handle(expr);
}
