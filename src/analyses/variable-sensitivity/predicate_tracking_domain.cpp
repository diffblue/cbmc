/*******************************************************************\

Module: Abstract Interpretation

Author: Martin Brain

Date: November 2022

\*******************************************************************/

#include "predicate_tracking_domain.h"

#include <util/namespace.h>

void predicate_tracking_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  variable_sensitivity_domaint::output(out, ai, ns);
}

exprt predicate_tracking_domaint::to_predicate() const
{
  return variable_sensitivity_domaint::to_predicate();
}

exprt predicate_tracking_domaint::to_predicate(
  const exprt &expr,
  const namespacet &ns) const
{
  return variable_sensitivity_domaint::to_predicate(expr, ns);
}

exprt predicate_tracking_domaint::to_predicate(
  const exprt::operandst &exprs,
  const namespacet &ns) const
{
  return variable_sensitivity_domaint::to_predicate(exprs, ns);
}

bool predicate_tracking_domaint::merge(
  const predicate_tracking_domaint &b,
  trace_ptrt from,
  trace_ptrt to)
{
  return variable_sensitivity_domaint::merge(b, from, to);
}

bool predicate_tracking_domaint::ai_simplify(
  exprt &condition,
  const namespacet &ns) const
{
  return variable_sensitivity_domaint::ai_simplify(condition, ns);
}

void predicate_tracking_domaint::merge_three_way_function_return(
  const ai_domain_baset &function_call,
  const ai_domain_baset &function_start,
  const ai_domain_baset &function_end,
  const namespacet &ns)
{
  variable_sensitivity_domaint::merge_three_way_function_return(
    function_call, function_start, function_end, ns);
  return;
}

void predicate_tracking_domaint::assume(exprt expr, namespacet ns)
{
  variable_sensitivity_domaint::assume(expr, ns);
}

bool predicate_tracking_domaint::assign(
  const exprt &expr,
  const abstract_object_pointert &value,
  const namespacet &ns)
{
  return variable_sensitivity_domaint::assign(expr, value, ns);
}
