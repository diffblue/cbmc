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
    : lower_extended(
        constant_interval_exprt::less_than(rhs.get_lower(), lhs.get_lower())),
      upper_extended(
        constant_interval_exprt::less_than(lhs.get_upper(), rhs.get_upper())),
      ns_(symbol_tablet{}),
      lower_(
        constant_interval_exprt::get_min(lhs.get_lower(), rhs.get_lower())),
      upper_(
        constant_interval_exprt::get_max(lhs.get_upper(), rhs.get_upper())),
      range_(
        plus_exprt(minus_exprt(upper_, lower_), from_integer(1, lhs.type()))),
      lower_bound(make_lower_bound()),
      upper_bound(make_upper_bound())
  {
  }

  const bool lower_extended;
  const bool upper_extended;

private:
  namespacet ns_;
  exprt lower_;
  exprt upper_;
  exprt range_;

public:
  const exprt lower_bound;
  const exprt upper_bound;

private:
  exprt make_lower_bound() const;
  exprt make_upper_bound() const;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WIDENED_RANGE_H
