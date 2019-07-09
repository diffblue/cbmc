/*******************************************************************\

Module: Interval constraint

Author: Jeannie Moulton

\*******************************************************************/

#include "interval_constraint.h"
#include "arith_tools.h"

exprt interval_constraint(const exprt &expr, const integer_intervalt &interval)
{
  // expr >= lower_bound && expr <= upper_bound
  return and_exprt(
    binary_relation_exprt(
      expr, ID_ge, from_integer(interval.lower, expr.type())),
    binary_relation_exprt(
      expr, ID_le, from_integer(interval.upper, expr.type())));
}
