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
static bool has_overflowed(const exprt &value, const exprt &initial_value)
{
  return constant_interval_exprt::less_than(value, initial_value);
}

exprt widened_ranget::widen_lower_bound() const
{
  if(!is_lower_widened)
    return lower_bound;

  auto new_lower_bound = simplify_expr(minus_exprt(lower_bound, range_), ns_);

  if(
    constant_interval_exprt::contains_extreme(new_lower_bound) ||
    has_underflowed(new_lower_bound))
    return min_exprt(lower_bound.type());

  return new_lower_bound;
}

exprt widened_ranget::widen_upper_bound() const
{
  if(!is_upper_widened)
    return upper_bound;

  auto new_upper_bound = simplify_expr(plus_exprt(upper_bound, range_), ns_);

  if(
    constant_interval_exprt::contains_extreme(new_upper_bound) ||
    has_overflowed(new_upper_bound, upper_bound))
    return max_exprt(upper_bound.type());

  return new_upper_bound;
}
