/*******************************************************************\

Module: Decision Procedure Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Decision Procedure Interface

#include "decision_procedure.h"

decision_proceduret::~decision_proceduret()
{
}

decision_proceduret::resultt decision_proceduret::operator()()
{
  return dec_solve();
}

void decision_proceduret::set_to_true(const exprt &expr)
{
  set_to(expr, true);
}

void decision_proceduret::set_to_false(const exprt &expr)
{
  set_to(expr, false);
}
