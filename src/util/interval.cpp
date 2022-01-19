/*******************************************************************\

 Module: intervals

 Author: Daniel Neville (2017), Diffblue Ltd

\*******************************************************************/

/*
 *
 * Types:  Should we store a type for the entire interval?
 * IMO: I think YES (for the case where we have -inf -> inf, we don't know otherwise
 *
 * This initial implementation only implements support for integers.
 */

#include "interval.h"

#include <ostream>

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "c_types.h"
#include "namespace.h"
#include "simplify_expr.h"
#include "std_expr.h"
#include "symbol_table.h"

const exprt &constant_interval_exprt::get_lower() const
{
  return op0();
}

const exprt &constant_interval_exprt::get_upper() const
{
  return op1();
}

constant_interval_exprt constant_interval_exprt::unary_plus() const
{
  return *this;
}

constant_interval_exprt constant_interval_exprt::unary_minus() const
{
  if(is_single_value_interval())
  {
    handle_constant_unary_expression(ID_unary_minus);
  }

  exprt lower;
  exprt upper;

  if(has_no_upper_bound())
  {
    lower = min();
  }
  else
  {
    lower = simplified_expr(unary_minus_exprt(get_upper()));
  }

  if(has_no_lower_bound())
  {
    upper = max();
  }
  else
  {
    upper = simplified_expr(unary_minus_exprt(get_lower()));
  }

  return constant_interval_exprt(lower, upper);
}

constant_interval_exprt
constant_interval_exprt::plus(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constant_binary_expression(o, ID_plus);
  }

  exprt lower = min();
  exprt upper = max();

  if(is_max(get_upper()) || is_max(o.get_upper()))
  {
    upper = max_exprt(type());
  }
  else
  {
    INVARIANT(
      !is_max(get_upper()) && !is_max(o.get_upper()),
      "We just excluded this case");
    upper = simplified_expr(plus_exprt(get_upper(), o.get_upper()));
  }

  if(is_min(get_lower()) || is_min(o.get_lower()))
  {
    lower = min_exprt(type());
  }
  else
  {
    INVARIANT(
      !is_min(get_lower()) && !is_min(o.get_lower()),
      "We just excluded that case");
    lower = simplified_expr(plus_exprt(get_lower(), o.get_lower()));
  }

  return simplified_interval(lower, upper);
}

constant_interval_exprt
constant_interval_exprt::minus(const constant_interval_exprt &other) const
{
  if(other.is_single_value_interval() && is_single_value_interval())
  {
    handle_constant_binary_expression(other, ID_minus);
  }

  // [this.lower - other.upper, this.upper - other.lower]
  return plus(other.unary_minus());
}

constant_interval_exprt
constant_interval_exprt::multiply(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constant_binary_expression(o, ID_mult);
  }

  return get_extremes(*this, o, ID_mult);
}

constant_interval_exprt
constant_interval_exprt::divide(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constant_binary_expression(o, ID_div);
  }

  // If other might be division by zero, set everything to top.
  if(o.contains_zero())
  {
    return top();
  }

  return get_extremes(*this, o, ID_div);
}

constant_interval_exprt
constant_interval_exprt::modulo(const constant_interval_exprt &o) const
{
  // SEE https://stackoverflow.com/questions/11720656/modulo-operation-with-negative-numbers

  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constant_binary_expression(o, ID_mod);
  }

  if(o.is_bottom())
  {
    return top();
  }

  // If the RHS is 1, or -1 (signed only), then return zero.
  if(
    o == constant_interval_exprt(from_integer(1, o.type())) ||
    (o.is_signed() && o == constant_interval_exprt(from_integer(-1, o.type()))))
  {
    return constant_interval_exprt(zero());
  }

  // If other might be modulo by zero, set everything to top.
  if(o.contains_zero())
  {
    return top();
  }

  if(is_zero())
  {
    return constant_interval_exprt(zero());
  }

  exprt lower = min();
  exprt upper = max();

  // Positive case (cannot have zero on RHS).
  // 10 % 5 = [0, 4], 3 % 5 = [0, 3]
  if(!is_negative() && o.is_positive())
  {
    lower = zero();
    upper = get_min(get_upper(), o.decrement().get_upper());
  }

  // [-5, 5] % [3]
  if(is_negative(get_lower()) && is_positive(get_upper()))
  {
    INVARIANT(
      contains_zero(),
      "Zero should be between a negative and a positive value");
    // This can be done more accurately.
    lower = get_min(o.get_lower(), get_lower());
    upper = get_max(o.get_upper(), get_upper());
  }

  if(is_negative() && o.is_negative())
  {
    lower = get_min(o.get_lower(), o.get_lower());
    upper = zero();
  }

  return constant_interval_exprt(lower, upper);
}

tvt constant_interval_exprt::is_definitely_true() const
{
  // tvt not
  return !is_definitely_false();
}

tvt constant_interval_exprt::is_definitely_false() const
{
  if(type().id() == ID_bool)
  {
    if(is_single_value_interval())
    {
      return tvt(get_lower() == false_exprt());
    }
    else
    {
      return tvt::unknown();
    }
  }

  if(equal(constant_interval_exprt(zero())).is_true())
  {
    return tvt(true);
  }

  if(contains(constant_interval_exprt(zero())))
  {
    INVARIANT(
      is_positive(get_upper()) || is_negative(get_lower()),
      "If an interval contains zero its lower bound can't be positive"
      " and its upper bound can't be negative");
    return tvt::unknown();
  }

  return tvt(false);
}

tvt constant_interval_exprt::logical_or(const constant_interval_exprt &o) const
{
  PRECONDITION(type().id() == ID_bool);
  PRECONDITION(o.type().id() == ID_bool);

  tvt a = is_definitely_true();
  tvt b = o.is_definitely_true();

  return (a || b);
}

tvt constant_interval_exprt::logical_and(const constant_interval_exprt &o) const
{
  PRECONDITION(type().id() == ID_bool);
  PRECONDITION(o.type().id() == ID_bool);

  return (is_definitely_true() && o.is_definitely_true());
}

tvt constant_interval_exprt::logical_xor(const constant_interval_exprt &o) const
{
  PRECONDITION(type().id() == ID_bool);
  PRECONDITION(o.type().id() == ID_bool);

  return (
    (is_definitely_true() && !o.is_definitely_true()) ||
    (!is_definitely_true() && o.is_definitely_true()));
}

tvt constant_interval_exprt::logical_not() const
{
  PRECONDITION(type().id() == ID_bool);

  if(is_definitely_true().is_true())
  {
    return tvt(false);
  }

  if(is_definitely_false().is_true())
  {
    return tvt(true);
  }

  return tvt::unknown();
}

constant_interval_exprt
constant_interval_exprt::left_shift(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    return handle_constant_binary_expression(o, ID_shl);
  }

  if(is_negative(o.get_lower()))
  {
    return top();
  }

  return get_extremes(*this, o, ID_shl);
}

// Arithmetic
constant_interval_exprt
constant_interval_exprt::right_shift(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    return handle_constant_binary_expression(o, ID_ashr);
  }

  if(is_negative(o.get_lower()))
  {
    return top();
  }

  return get_extremes(*this, o, ID_ashr);
}

constant_interval_exprt
constant_interval_exprt::bitwise_xor(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    return handle_constant_binary_expression(o, ID_bitxor);
  }

  return top();
}

constant_interval_exprt
constant_interval_exprt::bitwise_or(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    return handle_constant_binary_expression(o, ID_bitor);
  }

  return top();
}

constant_interval_exprt
constant_interval_exprt::bitwise_and(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    return handle_constant_binary_expression(o, ID_bitand);
  }

  return top();
}

constant_interval_exprt constant_interval_exprt::bitwise_not() const
{
  if(is_single_value_interval())
  {
    return handle_constant_unary_expression(ID_bitnot);
  }

  return top();
}

tvt constant_interval_exprt::less_than(const constant_interval_exprt &o) const
{
  // [get_lower, get_upper] < [o.get_lower(), o.get_upper()]
  if(is_single_value_interval() && o.is_single_value_interval())
  {
    return tvt(less_than(get_lower(), o.get_lower()));
  }

  if(less_than(get_upper(), o.get_lower()))
  {
    return tvt(true);
  }

  if(greater_than(get_lower(), o.get_upper()))
  {
    return tvt(false);
  }

  return tvt::unknown();
}

tvt constant_interval_exprt::greater_than(
  const constant_interval_exprt &o) const
{
  return o.less_than(*this);
}

tvt constant_interval_exprt::less_than_or_equal(
  const constant_interval_exprt &o) const
{
  if(is_single_value_interval() && o.is_single_value_interval())
  {
    return tvt(less_than_or_equal(get_lower(), o.get_lower()));
  }

  // [get_lower, get_upper] <= [o.get_lower(), o.get_upper()]
  if(less_than_or_equal(get_upper(), o.get_lower()))
  {
    return tvt(true);
  }

  if(greater_than(get_lower(), o.get_upper()))
  {
    return tvt(false);
  }

  return tvt::unknown();
}

tvt constant_interval_exprt::greater_than_or_equal(
  const constant_interval_exprt &o) const
{
  return o.less_than_or_equal(*this);
}

tvt constant_interval_exprt::equal(const constant_interval_exprt &o) const
{
  if(is_single_value_interval() && o.is_single_value_interval())
  {
    return tvt(equal(get_lower(), o.get_lower()));
  }

  if(equal(get_upper(), o.get_upper()) && equal(get_lower(), o.get_lower()))
  {
    return tvt(true);
  }

  if(
    less_than(o).is_true() || greater_than(o).is_true() ||
    o.less_than(*this).is_true() || o.greater_than(*this).is_true())
  {
    return tvt(false);
  }

  // Don't know.  Could have [3, 5] == [4] (not equal)
  return tvt::unknown();
}

tvt constant_interval_exprt::not_equal(const constant_interval_exprt &o) const
{
  return !equal(o);
}

constant_interval_exprt constant_interval_exprt::increment() const
{
  return plus(constant_interval_exprt(from_integer(mp_integer(1), type())));
}

constant_interval_exprt constant_interval_exprt::decrement() const
{
  return minus(constant_interval_exprt(from_integer(mp_integer(1), type())));
}

constant_interval_exprt constant_interval_exprt::get_extremes(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b,
  const irep_idt &operation)
{
  std::vector<exprt> results;

  generate_expression(a.get_lower(), b.get_lower(), operation, results);
  generate_expression(a.get_lower(), b.get_upper(), operation, results);
  generate_expression(a.get_upper(), b.get_lower(), operation, results);
  generate_expression(a.get_upper(), b.get_upper(), operation, results);

  for(auto result : results)
  {
    if(!is_extreme(result) && contains_extreme(result))
    {
      return constant_interval_exprt(result.type());
    }
  }

  exprt min = get_min(results);
  exprt max = get_max(results);

  return simplified_interval(min, max);
}

exprt constant_interval_exprt::get_extreme(
  std::vector<exprt> values,
  bool min_value)
{
  symbol_tablet symbol_table;
  namespacet ns(symbol_table); // Empty

  if(values.size() == 0)
  {
    return nil_exprt();
  }

  if(values.size() == 1)
  {
    return *(values.begin());
  }

  if(values.size() == 2)
  {
    if(min_value)
    {
      return get_min(values.front(), values.back());
    }
    else
    {
      return get_max(values.front(), values.back());
    }
  }

  typet type = values.begin()->type();

  for(auto v : values)
  {
    if((min_value && is_min(v)) || (!min_value && is_max(v)))
    {
      return v;
    }
  }

  for(auto left : values)
  {
    bool all_left_OP_right = true;

    for(auto right : values)
    {
      if(
        (min_value && less_than_or_equal(left, right)) ||
        (!min_value && greater_than_or_equal(left, right)))
      {
        continue;
      }

      all_left_OP_right = false;
      break;
    }

    if(all_left_OP_right)
    {
      return left;
    }
  }

  /* Return top */
  if(min_value)
  {
    return min_exprt(type);
  }
  else
  {
    return max_exprt(type);
  }

  UNREACHABLE;
}

void constant_interval_exprt::generate_expression(
  const exprt &lhs,
  const exprt &rhs,
  const irep_idt &operation,
  std::vector<exprt> &collection)
{
  if(operation == ID_mult)
  {
    append_multiply_expression(lhs, rhs, collection);
  }
  else if(operation == ID_div)
  {
    collection.push_back(generate_division_expression(lhs, rhs));
  }
  else if(operation == ID_mod)
  {
    collection.push_back(generate_modulo_expression(lhs, rhs));
  }
  else if(operation == ID_shl || operation == ID_ashr)
  {
    collection.push_back(generate_shift_expression(lhs, rhs, operation));
  }
}

/// Adds all possible values that may arise from multiplication (more than one,
/// in case of past the type boundary results).
/// \param lower lhs of multiplication
/// \param upper rhs of multiplication
/// \param collection vector of possible values
void constant_interval_exprt::append_multiply_expression(
  const exprt &lower,
  const exprt &upper,
  std::vector<exprt> &collection)
{
  PRECONDITION(lower.type().is_not_nil() && is_numeric(lower.type()));

  if(is_max(lower))
  {
    append_multiply_expression_max(upper, collection);
  }
  else if(is_max(upper))
  {
    append_multiply_expression_max(lower, collection);
  }
  else if(is_min(lower))
  {
    append_multiply_expression_min(lower, upper, collection);
  }
  else if(is_min(upper))
  {
    append_multiply_expression_min(upper, lower, collection);
  }
  else
  {
    INVARIANT(
      !is_extreme(lower) && !is_extreme(upper),
      "We ruled out extreme cases beforehand");

    auto result = mult_exprt(lower, upper);
    collection.push_back(simplified_expr(result));
  }
}

/// Appends interval bounds that could arise from MAX * expr. Accommodates for
/// overflows by over-approximating.
/// \param expr the unknown side of multiplication
/// \param collection vector of collected bounds
void constant_interval_exprt::append_multiply_expression_max(
  const exprt &expr,
  std::vector<exprt> &collection)
{
  if(is_min(expr))
  {
    INVARIANT(!is_positive(expr), "Min value cannot be >0.");
    INVARIANT(
      is_negative(expr) || is_zero(expr), "Non-negative MIN must be zero.");
  }

  if(is_zero(expr))
    collection.push_back(expr);
  else
  {
    collection.push_back(max_exprt(expr));
    collection.push_back(min_exprt(expr));
  }
}

/// Appends interval bounds that could arise from MIN * other. Accommodates for
/// overflows by over-approximating.
/// \param min the side known to be MIN for a given type
/// \param other the side of unknown value
/// \param collection reference to the vector of collected boundaries
void constant_interval_exprt::append_multiply_expression_min(
  const exprt &min,
  const exprt &other,
  std::vector<exprt> &collection)
{
  PRECONDITION(is_min(min));
  INVARIANT(!is_positive(min), "Min value cannot be >0.");
  INVARIANT(is_negative(min) || is_zero(min), "Non-negative MIN must be zero.");

  if(is_zero(min))
    collection.push_back(min);
  else if(is_zero(other))
    collection.push_back(other);
  else
  {
    collection.push_back(min_exprt(min));
    collection.push_back(max_exprt(min));
  }
}

exprt constant_interval_exprt::generate_division_expression(
  const exprt &lhs,
  const exprt &rhs)
{
  PRECONDITION(lhs.type().is_not_nil() && is_numeric(lhs.type()));

  PRECONDITION(!is_zero(rhs));

  if(rhs.is_one())
  {
    return lhs;
  }

  if(is_max(lhs))
  {
    if(is_negative(rhs))
    {
      return min_exprt(lhs);
    }

    return lhs;
  }

  if(is_min(lhs))
  {
    if(is_negative(rhs))
    {
      return max_exprt(lhs);
    }

    return lhs;
  }

  INVARIANT(!is_extreme(lhs), "We ruled out extreme cases beforehand");

  if(is_max(rhs))
  {
    return zero(rhs);
  }

  if(is_min(rhs))
  {
    INVARIANT(
      is_signed(rhs), "We think this is a signed integer for some reason?");
    return zero(rhs);
  }

  INVARIANT(
    !is_extreme(lhs) && !is_extreme(rhs),
    "We ruled out extreme cases beforehand");

  auto div_expr = div_exprt(lhs, rhs);
  return simplified_expr(div_expr);
}

exprt constant_interval_exprt::generate_modulo_expression(
  const exprt &lhs,
  const exprt &rhs)
{
  PRECONDITION(lhs.type().is_not_nil() && is_numeric(lhs.type()));

  PRECONDITION(!is_zero(rhs));

  if(rhs.is_one())
  {
    return lhs;
  }

  if(is_max(lhs))
  {
    if(is_negative(rhs))
    {
      return min_exprt(lhs);
    }

    return lhs;
  }

  if(is_min(lhs))
  {
    if(is_negative(rhs))
    {
      return max_exprt(lhs);
    }

    return lhs;
  }

  INVARIANT(!is_extreme(lhs), "We rule out this case beforehand");

  if(is_max(rhs))
  {
    return zero(rhs);
  }

  if(is_min(rhs))
  {
    INVARIANT(is_signed(rhs), "We assume this is signed for some reason?");
    return zero(rhs);
  }

  INVARIANT(
    !is_extreme(lhs) && !is_extreme(rhs),
    "We ruled out extreme values beforehand");

  auto modulo_expr = mod_exprt(lhs, rhs);
  return simplified_expr(modulo_expr);
}

constant_interval_exprt constant_interval_exprt::eval(const irep_idt &id) const
{
  if(id == ID_unary_plus)
  {
    return unary_plus();
  }
  if(id == ID_unary_minus)
  {
    return unary_minus();
  }
  if(id == ID_bitnot)
  {
    return bitwise_not();
  }
  if(id == ID_not)
  {
    return tvt_to_interval(logical_not());
  }

  return top();
}

constant_interval_exprt constant_interval_exprt::eval(
  const irep_idt &binary_operator,
  const constant_interval_exprt &other) const
{
  if(binary_operator == ID_plus)
  {
    return plus(other);
  }
  if(binary_operator == ID_minus)
  {
    return minus(other);
  }
  if(binary_operator == ID_mult)
  {
    return multiply(other);
  }
  if(binary_operator == ID_div)
  {
    return divide(other);
  }
  if(binary_operator == ID_mod)
  {
    return modulo(other);
  }
  if(binary_operator == ID_shl)
  {
    return left_shift(other);
  }
  if(binary_operator == ID_ashr)
  {
    return right_shift(other);
  }
  if(binary_operator == ID_bitor)
  {
    return bitwise_or(other);
  }
  if(binary_operator == ID_bitand)
  {
    return bitwise_and(other);
  }
  if(binary_operator == ID_bitxor)
  {
    return bitwise_xor(other);
  }
  if(binary_operator == ID_lt)
  {
    return tvt_to_interval(less_than(other));
  }
  if(binary_operator == ID_le)
  {
    return tvt_to_interval(less_than_or_equal(other));
  }
  if(binary_operator == ID_gt)
  {
    return tvt_to_interval(greater_than(other));
  }
  if(binary_operator == ID_ge)
  {
    return tvt_to_interval(greater_than_or_equal(other));
  }
  if(binary_operator == ID_equal)
  {
    return tvt_to_interval(equal(other));
  }
  if(binary_operator == ID_notequal)
  {
    return tvt_to_interval(not_equal(other));
  }
  if(binary_operator == ID_and)
  {
    return tvt_to_interval(logical_and(other));
  }
  if(binary_operator == ID_or)
  {
    return tvt_to_interval(logical_or(other));
  }
  if(binary_operator == ID_xor)
  {
    return tvt_to_interval(logical_xor(other));
  }

  return top();
}

exprt constant_interval_exprt::generate_shift_expression(
  const exprt &lhs,
  const exprt &rhs,
  const irep_idt &operation)
{
  PRECONDITION(operation == ID_shl || operation == ID_ashr);

  if(is_zero(lhs) || is_zero(rhs))
  {
    // Shifting zero does nothing.
    // Shifting BY zero also does nothing.
    return lhs;
  }

  INVARIANT(!is_negative(rhs), "Should be caught at an earlier stage.");

  if(is_max(lhs))
  {
    return lhs;
  }

  if(is_min(lhs))
  {
    return lhs;
  }

  if(is_max(rhs))
  {
    return min_exprt(rhs);
  }

  INVARIANT(
    !is_extreme(lhs) && !is_extreme(rhs),
    "We ruled out extreme cases beforehand");

  auto shift_expr = shift_exprt(lhs, operation, rhs);
  return simplified_expr(shift_expr);
}

constant_interval_exprt
constant_interval_exprt::handle_constant_unary_expression(
  const irep_idt &op) const
{
  if(is_single_value_interval())
  {
    auto expr = unary_exprt(op, get_lower());
    return constant_interval_exprt(simplified_expr(expr));
  }
  return top();
}

constant_interval_exprt
constant_interval_exprt::handle_constant_binary_expression(
  const constant_interval_exprt &other,
  const irep_idt &op) const
{
  PRECONDITION(is_single_value_interval() && other.is_single_value_interval());
  auto expr = binary_exprt(get_lower(), op, other.get_lower());
  return constant_interval_exprt(simplified_expr(expr));
}

exprt constant_interval_exprt::get_max(const exprt &a, const exprt &b)
{
  return greater_than(a, b) ? a : b;
}

exprt constant_interval_exprt::get_min(const exprt &a, const exprt &b)
{
  return less_than(a, b) ? a : b;
}

exprt constant_interval_exprt::get_min(std::vector<exprt> &values)
{
  return get_extreme(values, true);
}

exprt constant_interval_exprt::get_max(std::vector<exprt> &values)
{
  return get_extreme(values, false);
}

/* we don't simplify in the constructor otherwise */
constant_interval_exprt
constant_interval_exprt::simplified_interval(exprt &l, exprt &r)
{
  return constant_interval_exprt(simplified_expr(l), simplified_expr(r));
}

exprt constant_interval_exprt::simplified_expr(exprt expr)
{
  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  PRECONDITION(!contains_extreme(expr));

  return simplify_expr(expr, ns);
}

constant_exprt constant_interval_exprt::zero(const typet &type)
{
  constant_exprt zero = from_integer(mp_integer(0), type);
  INVARIANT(
    zero.is_zero() || (type.id() == ID_bool && zero.is_false()),
    "The value created from 0 should be zero or false");
  return zero;
}

constant_exprt constant_interval_exprt::zero(const exprt &expr)
{
  return zero(expr.type());
}

constant_exprt
constant_interval_exprt::zero(const constant_interval_exprt &interval)
{
  return zero(interval.type());
}

constant_exprt constant_interval_exprt::zero() const
{
  return zero(type());
}

min_exprt constant_interval_exprt::min() const
{
  return min_exprt(type());
}

max_exprt constant_interval_exprt::max() const
{
  return max_exprt(type());
}

bool constant_interval_exprt::is_top() const
{
  return (has_no_lower_bound() && has_no_upper_bound());
}

bool constant_interval_exprt::is_bottom() const
{
  // This should ONLY happen for bottom.
  return is_min(get_upper()) || is_max(get_lower());
}

constant_interval_exprt constant_interval_exprt::top(const typet &type)
{
  return constant_interval_exprt(type);
}

constant_interval_exprt constant_interval_exprt::bottom(const typet &type)
{
  return constant_interval_exprt(max_exprt(type), min_exprt(type));
}

constant_interval_exprt constant_interval_exprt::top() const
{
  return constant_interval_exprt(type());
}

constant_interval_exprt constant_interval_exprt::bottom() const
{
  return bottom(type());
}

/* Helpers */

bool constant_interval_exprt::is_int() const
{
  return is_int(type());
}

bool constant_interval_exprt::is_float() const
{
  return is_float(type());
}

bool constant_interval_exprt::is_numeric(const typet &type)
{
  return is_int(type) || is_float(type);
}

bool constant_interval_exprt::is_numeric() const
{
  return is_numeric(type());
}

bool constant_interval_exprt::is_numeric(const exprt &expr)
{
  return is_numeric(expr.type());
}

bool constant_interval_exprt::is_numeric(
  const constant_interval_exprt &interval)
{
  return interval.is_numeric();
}

bool constant_interval_exprt::is_int(const typet &type)
{
  return (is_signed(type) || is_unsigned(type));
}

bool constant_interval_exprt::is_float(const typet &src)
{
  return src.id() == ID_floatbv;
}

bool constant_interval_exprt::is_int(const exprt &expr)
{
  return is_int(expr.type());
}

bool constant_interval_exprt::is_int(const constant_interval_exprt &interval)
{
  return interval.is_int();
}

bool constant_interval_exprt::is_float(const exprt &expr)
{
  return is_float(expr.type());
}

bool constant_interval_exprt::is_float(const constant_interval_exprt &interval)
{
  return interval.is_float();
}

bool constant_interval_exprt::is_bitvector(const typet &t)
{
  return t.id() == ID_bv || t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
         t.id() == ID_c_bool ||
         (t.id() == ID_c_bit_field &&
          is_bitvector(to_c_bit_field_type(t).underlying_type()));
}

bool constant_interval_exprt::is_signed(const typet &t)
{
  return t.id() == ID_signedbv ||
         (t.id() == ID_c_bit_field &&
          is_signed(to_c_bit_field_type(t).underlying_type()));
}

bool constant_interval_exprt::is_unsigned(const typet &t)
{
  return t.id() == ID_bv || t.id() == ID_unsignedbv || t.id() == ID_c_bool ||
         t.id() == ID_c_enum ||
         (t.id() == ID_c_bit_field &&
          is_unsigned(to_c_bit_field_type(t).underlying_type()));
}

bool constant_interval_exprt::is_signed(const constant_interval_exprt &interval)
{
  return is_signed(interval.type());
}

bool constant_interval_exprt::is_unsigned(
  const constant_interval_exprt &interval)
{
  return is_unsigned(interval.type());
}

bool constant_interval_exprt::is_bitvector(
  const constant_interval_exprt &interval)
{
  return is_bitvector(interval.type());
}

bool constant_interval_exprt::is_signed(const exprt &expr)
{
  return is_signed(expr.type());
}

bool constant_interval_exprt::is_unsigned(const exprt &expr)
{
  return is_unsigned(expr.type());
}

bool constant_interval_exprt::is_bitvector(const exprt &expr)
{
  return is_bitvector(expr.type());
}

bool constant_interval_exprt::is_signed() const
{
  return is_signed(type());
}

bool constant_interval_exprt::is_unsigned() const
{
  return is_unsigned(type());
}

bool constant_interval_exprt::is_bitvector() const
{
  return is_bitvector(type());
}

bool constant_interval_exprt::is_extreme(const exprt &expr)
{
  return (is_max(expr) || is_min(expr));
}

bool constant_interval_exprt::is_extreme(const exprt &expr1, const exprt &expr2)
{
  return is_extreme(expr1) || is_extreme(expr2);
}

bool constant_interval_exprt::has_no_upper_bound() const
{
  return is_max(get_upper());
}

bool constant_interval_exprt::has_no_lower_bound() const
{
  return is_min(get_lower());
}

bool constant_interval_exprt::is_max(const exprt &expr)
{
  return expr.id() == ID_max;
}

bool constant_interval_exprt::is_min(const exprt &expr)
{
  return expr.id() == ID_min;
}

bool constant_interval_exprt::is_positive(const exprt &expr)
{
  exprt simplified = simplified_expr(expr);

  if(expr.is_nil() || !simplified.is_constant() || expr.get(ID_value) == "")
  {
    return false;
  }

  if(is_unsigned(expr) || is_max(expr))
  {
    return true;
  }

  INVARIANT(is_signed(expr), "Not implemented for floats");
  // Floats later

  if(is_min(expr))
  {
    return false;
  }

  return greater_than(expr, zero(expr));
}

bool constant_interval_exprt::is_zero(const exprt &expr)
{
  if(is_min(expr))
  {
    if(is_unsigned(expr))
    {
      return true;
    }
    else
    {
      return false;
    }
  }

  if(is_max(expr))
  {
    return false;
  }

  INVARIANT(!is_max(expr) && !is_min(expr), "We excluded those cases");

  if(expr.is_zero())
  {
    return true;
  }

  return equal(expr, zero(expr));
}

bool constant_interval_exprt::is_negative(const exprt &expr)
{
  if(is_unsigned(expr) || is_max(expr))
  {
    return false;
  }

  INVARIANT(
    is_signed(expr), "We don't support anything other than integers yet");

  if(is_min(expr))
  {
    return true;
  }

  INVARIANT(!is_extreme(expr), "We excluded these cases before");

  return less_than(expr, zero(expr));
}

exprt constant_interval_exprt::abs(const exprt &expr)
{
  if(is_signed(expr) && is_min(expr))
  {
    return max_exprt(expr);
  }

  if(is_max(expr) || is_unsigned(expr) || is_zero(expr) || is_positive(expr))
  {
    return expr;
  }

  return simplified_expr(unary_minus_exprt(expr));
}

bool constant_interval_exprt::equal(const exprt &a, const exprt &b)
{
  if(a == b)
  {
    return true;
  }

  if(!is_numeric(a) || !is_numeric(b))
  {
    INVARIANT(
      !(a == b),
      "Best we can do now is a==b?, but this is covered by the above, so "
      "always false");
    return false;
  }

  if(is_max(a) && is_max(b))
  {
    return true;
  }

  exprt l = (is_min(a) && is_unsigned(a)) ? zero(a) : a;
  exprt r = (is_min(b) && is_unsigned(b)) ? zero(b) : b;

  // CANNOT use is_zero(X) but can use X.is_zero();
  if((is_min(l) && is_min(r)))
  {
    return true;
  }

  if(
    (is_max(l) && !is_max(r)) || (is_min(l) && !is_min(r)) ||
    (is_max(r) && !is_max(l)) || (is_min(r) && !is_min(l)))
  {
    return false;
  }

  INVARIANT(!is_extreme(l, r), "We've excluded this before");

  return simplified_expr(equal_exprt(l, r)).is_true();
}

// TODO: Signed/unsigned comparisons.
bool constant_interval_exprt::less_than(const exprt &a, const exprt &b)
{
  if(!is_numeric(a) || !is_numeric(b))
  {
    return false;
  }

  exprt l = (is_min(a) && is_unsigned(a)) ? zero(a) : a;
  exprt r = (is_min(b) && is_unsigned(b)) ? zero(b) : b;

  if(is_max(l))
  {
    return false;
  }

  INVARIANT(!is_max(l), "We've just excluded this case");

  if(is_min(r))
  {
    // Can't be smaller than min.
    return false;
  }

  INVARIANT(!is_max(l) && !is_min(r), "We've excluded these cases");

  if(is_min(l))
  {
    return true;
  }

  INVARIANT(
    !is_max(l) && !is_min(r) && !is_min(l),
    "These cases should have all been handled before this point");

  if(is_max(r))
  {
    // If r is max, then l is less, unless l is max.
    return !is_max(l);
  }

  INVARIANT(
    !is_extreme(l) && !is_extreme(r),
    "We have excluded all of these cases in the code above");

  return simplified_expr(binary_relation_exprt(l, ID_lt, r)).is_true();
}

bool constant_interval_exprt::greater_than(const exprt &a, const exprt &b)
{
  return less_than(b, a);
}

bool constant_interval_exprt::less_than_or_equal(const exprt &a, const exprt &b)
{
  return less_than(a, b) || equal(a, b);
}

bool constant_interval_exprt::greater_than_or_equal(
  const exprt &a,
  const exprt &b)
{
  return greater_than(a, b) || equal(a, b);
}

bool constant_interval_exprt::not_equal(const exprt &a, const exprt &b)
{
  return !equal(a, b);
}

bool constant_interval_exprt::contains(
  const constant_interval_exprt &interval) const
{
  // [a, b] Contains [c, d] If c >= a and d <= b.
  return (
    less_than_or_equal(interval.get_upper(), get_upper()) &&
    greater_than_or_equal(interval.get_lower(), get_lower()));
}

std::string constant_interval_exprt::to_string() const
{
  std::stringstream out;
  out << *this;
  return out.str();
}

std::ostream &operator<<(std::ostream &out, const constant_interval_exprt &i)
{
  out << "[";

  if(!i.has_no_lower_bound())
  {
    // FIXME Not everything that's a bitvector is also an integer
    if(i.is_bitvector(i.get_lower()))
    {
      out << integer2string(*numeric_cast<mp_integer>(i.get_lower()));
    }
    else
    {
      // TODO handle floating point numbers?
      out << i.get_lower().get(ID_value);
    }
  }
  else
  {
    if(i.is_signed(i.get_lower()))
    {
      out << "MIN";
    }
    else
    {
      // FIXME Extremely sketchy, the opposite of
      // FIXME "signed" isn't "unsigned" but
      // FIXME "literally anything else"
      out << "0";
    }
  }

  out << ",";

  // FIXME See comments on is_min
  if(!i.has_no_upper_bound())
  {
    if(i.is_bitvector(i.get_upper()))
    {
      out << integer2string(*numeric_cast<mp_integer>(i.get_upper()));
    }
    else
    {
      out << i.get_upper().get(ID_value);
    }
  }
  else
    out << "MAX";

  out << "]";

  return out;
}

bool operator<(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.less_than(rhs).is_true();
}

bool operator>(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.greater_than(rhs).is_true();
}

bool operator<=(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.less_than_or_equal(rhs).is_true();
}

bool operator>=(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.greater_than(rhs).is_true();
}

bool operator==(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.equal(rhs).is_true();
}

bool operator!=(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.not_equal(rhs).is_true();
}

const constant_interval_exprt operator+(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.unary_plus(rhs);
}

const constant_interval_exprt operator-(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.minus(rhs);
}

const constant_interval_exprt operator/(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.divide(rhs);
}

const constant_interval_exprt operator*(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.multiply(rhs);
}

const constant_interval_exprt operator%(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.modulo(rhs);
}

const constant_interval_exprt operator&(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.bitwise_and(rhs);
}

const constant_interval_exprt operator|(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.bitwise_or(rhs);
}

const constant_interval_exprt operator^(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.bitwise_xor(rhs);
}

const constant_interval_exprt operator!(const constant_interval_exprt &lhs)
{
  return lhs.bitwise_not();
}

const constant_interval_exprt operator<<(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.left_shift(rhs);
}

const constant_interval_exprt operator>>(
  const constant_interval_exprt &lhs,
  const constant_interval_exprt &rhs)
{
  return lhs.right_shift(rhs);
}

constant_interval_exprt
constant_interval_exprt::unary_plus(const constant_interval_exprt &a)
{
  return a.unary_plus();
}

constant_interval_exprt
constant_interval_exprt::unary_minus(const constant_interval_exprt &a)
{
  return a.unary_minus();
}

constant_interval_exprt
constant_interval_exprt::typecast(const typet &type) const
{
  if(this->type().id() == ID_bool && is_int(type))
  {
    bool lower = !has_no_lower_bound() && get_lower().is_true();
    bool upper = has_no_upper_bound() || get_upper().is_true();

    INVARIANT(!lower || upper, "");

    constant_exprt lower_num = from_integer(lower, type);
    constant_exprt upper_num = from_integer(upper, type);

    return constant_interval_exprt(lower_num, upper_num, type);
  }
  else
  {
    auto do_typecast = [&type](exprt e) {
      if(e.id() == ID_min || e.id() == ID_max)
      {
        e.type() = type;
      }
      else
      {
        e = simplified_expr(typecast_exprt(e, type));
      }
      return e;
    };

    exprt lower = do_typecast(get_lower());
    POSTCONDITION(lower.id() == get_lower().id());

    exprt upper = do_typecast(get_upper());
    POSTCONDITION(upper.id() == get_upper().id());

    return constant_interval_exprt(lower, upper, type);
  }
}

/* Binary */
constant_interval_exprt constant_interval_exprt::plus(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.plus(b);
}

constant_interval_exprt constant_interval_exprt::minus(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.minus(b);
}

constant_interval_exprt constant_interval_exprt::multiply(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.multiply(b);
}

constant_interval_exprt constant_interval_exprt::divide(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.divide(b);
}

constant_interval_exprt constant_interval_exprt::modulo(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.modulo(b);
}

/* Binary shifts */
constant_interval_exprt constant_interval_exprt::left_shift(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.left_shift(b);
}

constant_interval_exprt constant_interval_exprt::right_shift(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.right_shift(b);
}

/* Unary bitwise */
constant_interval_exprt
constant_interval_exprt::bitwise_not(const constant_interval_exprt &a)
{
  return a.bitwise_not();
}

/* Binary bitwise */
constant_interval_exprt constant_interval_exprt::bitwise_xor(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.bitwise_xor(b);
}

constant_interval_exprt constant_interval_exprt::bitwise_or(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.bitwise_or(b);
}

constant_interval_exprt constant_interval_exprt::bitwise_and(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.bitwise_and(b);
}

tvt constant_interval_exprt::less_than(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.less_than(b);
}

tvt constant_interval_exprt::greater_than(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.greater_than(b);
}

tvt constant_interval_exprt::less_than_or_equal(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.less_than_or_equal(b);
}

tvt constant_interval_exprt::greater_than_or_equal(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.greater_than_or_equal(b);
}

tvt constant_interval_exprt::equal(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.equal(b);
}

tvt constant_interval_exprt::not_equal(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.equal(b);
}

constant_interval_exprt
constant_interval_exprt::increment(const constant_interval_exprt &a)
{
  return a.increment();
}

constant_interval_exprt
constant_interval_exprt::decrement(const constant_interval_exprt &a)
{
  return a.decrement();
}

bool constant_interval_exprt::is_empty(const constant_interval_exprt &a)
{
  return a.is_empty();
}

bool constant_interval_exprt::is_single_value_interval(
  const constant_interval_exprt &a)
{
  return a.is_single_value_interval();
}

bool constant_interval_exprt::is_top(const constant_interval_exprt &a)
{
  return a.is_top();
}

bool constant_interval_exprt::is_bottom(const constant_interval_exprt &a)
{
  return a.is_bottom();
}

bool constant_interval_exprt::is_min(const constant_interval_exprt &a)
{
  return a.has_no_lower_bound();
}

bool constant_interval_exprt::is_max(const constant_interval_exprt &a)
{
  return a.has_no_upper_bound();
}

bool constant_interval_exprt::contains_extreme(const exprt expr)
{
  forall_operands(it, expr)
  {
    if(is_extreme(*it))
    {
      return true;
    }

    if(it->has_operands())
    {
      return contains_extreme(*it);
    }
  }

  return false;
}

bool constant_interval_exprt::contains_extreme(
  const exprt expr1,
  const exprt expr2)
{
  return contains_extreme(expr1) || contains_extreme(expr2);
}

bool constant_interval_exprt::is_empty() const
{
  if(greater_than(get_lower(), get_upper()))
  {
    return false;
  }

  return true;
}

bool constant_interval_exprt::is_single_value_interval() const
{
  return !is_extreme(get_lower()) && !is_extreme(get_upper()) &&
         equal(get_lower(), get_upper());
}

bool constant_interval_exprt::contains_zero() const
{
  if(!is_numeric())
  {
    return false;
  }

  if(get_lower().is_zero() || get_upper().is_zero())
  {
    return true;
  }

  if(is_unsigned() && is_min(get_lower()))
  {
    return true;
  }

  if(
    less_than_or_equal(get_lower(), zero()) &&
    greater_than_or_equal(get_upper(), zero()))
  {
    return true;
  }

  return false;
}

bool constant_interval_exprt::is_positive(
  const constant_interval_exprt &interval)
{
  return interval.is_positive();
}

bool constant_interval_exprt::is_zero(const constant_interval_exprt &interval)
{
  return interval.is_zero();
}

bool constant_interval_exprt::is_negative(
  const constant_interval_exprt &interval)
{
  return interval.is_negative();
}

bool constant_interval_exprt::is_positive() const
{
  return is_positive(get_lower()) && is_positive(get_upper());
}

bool constant_interval_exprt::is_zero() const
{
  return is_zero(get_lower()) && is_zero(get_upper());
}

bool constant_interval_exprt::is_negative() const
{
  return is_negative(get_lower()) && is_negative(get_upper());
}

tvt constant_interval_exprt::is_true(const constant_interval_exprt &a)
{
  return a.is_definitely_true();
}

tvt constant_interval_exprt::is_false(const constant_interval_exprt &a)
{
  return a.is_definitely_false();
}

tvt constant_interval_exprt::logical_and(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.logical_and(b);
}

tvt constant_interval_exprt::logical_or(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.logical_or(b);
}

tvt constant_interval_exprt::logical_xor(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.logical_xor(b);
}

tvt constant_interval_exprt::logical_not(const constant_interval_exprt &a)
{
  return a.logical_not();
}

constant_interval_exprt constant_interval_exprt::tvt_to_interval(const tvt &val)
{
  if(val.is_true())
  {
    return constant_interval_exprt(true_exprt());
  }
  else if(val.is_false())
  {
    return constant_interval_exprt(false_exprt());
  }
  else
  {
    return constant_interval_exprt(bool_typet());
  }
}
