/*******************************************************************\

 Module: helper for extending intervals during widening merges

 Author: Jez Higgins

\*******************************************************************/

#include "widened_range.h"
#include <util/simplify_expr.h>

static bool has_underflowed(const exprt &value)
{
  return constant_interval_exprt::greater_than(
    value, from_integer(0, value.type()));
}
static bool has_overflowed(const exprt &value)
{
  return constant_interval_exprt::less_than(
    value, from_integer(0, value.type()));
}

exprt widened_ranget::make_lower_bound() const
{
  if(!lower_extended)
    return lower_;

  auto new_lower_bound = simplify_expr(minus_exprt(lower_, range_), ns_);

  if(
    constant_interval_exprt::contains_extreme(new_lower_bound) ||
    has_underflowed(new_lower_bound))
    return min_exprt(lower_.type());

  return new_lower_bound;
}

exprt widened_ranget::make_upper_bound() const
{
  if(!upper_extended)
    return upper_;

  auto new_upper_bound = simplify_expr(plus_exprt(upper_, range_), ns_);

  if(
    constant_interval_exprt::contains_extreme(new_upper_bound) ||
    has_overflowed(new_upper_bound))
    return max_exprt(upper_.type());

  return new_upper_bound;
}
