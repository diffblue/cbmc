/*******************************************************************\

 Module: helper for extending intervals during widening merges

 Author: Jez Higgins

\*******************************************************************/

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WIDENED_RANGE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WIDENED_RANGE_H

#include <util/arith_tools.h>
#include <util/interval.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

class widened_ranget
{
public:
  widened_ranget(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs)
    : is_lower_widened(
        constant_interval_exprt::less_than(rhs.get_lower(), lhs.get_lower())),
      is_upper_widened(
        constant_interval_exprt::less_than(lhs.get_upper(), rhs.get_upper())),
      lower_bound(
        constant_interval_exprt::get_min(lhs.get_lower(), rhs.get_lower())),
      upper_bound(
        constant_interval_exprt::get_max(lhs.get_upper(), rhs.get_upper())),
      ns_(symbol_tablet{}),
      range_(plus_exprt(
        minus_exprt(upper_bound, lower_bound),
        from_integer(1, lhs.type()))),
      widened_lower_bound(widen_lower_bound()),
      widened_upper_bound(widen_upper_bound())
  {
  }

  const bool is_lower_widened;
  const bool is_upper_widened;
  const exprt lower_bound;
  const exprt upper_bound;

private:
  namespacet ns_;
  exprt range_;

public:
  const exprt widened_lower_bound;
  const exprt widened_upper_bound;

private:
  exprt widen_lower_bound() const;
  exprt widen_upper_bound() const;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WIDENED_RANGE_H
