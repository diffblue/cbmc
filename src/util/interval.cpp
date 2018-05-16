/*
 * interval.cpp
 *
 *  Created on: 16 Jun 2017
 *      Author: dan
 */

/*
 *
 * Types:  Should we store a type for the entire interval?
 * IMO: I think YES (for the case where we have -inf -> inf, we don't know otherwise
 *
 * This initial implementation only implements support for integers.
 */

#include "interval.h"

#include <ostream>
#include <sstream>
#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

const exprt &constant_interval_exprt::get_lower() const
{
  return op0();
}

const exprt &constant_interval_exprt::get_upper() const
{
  return op1();
}

//make clean -s && make -j 7 CXX="/usr/local/bin/ccache g++" -s && ./unit_tests

const constant_interval_exprt constant_interval_exprt::unary_plus() const
{
  return *this;
}

const constant_interval_exprt constant_interval_exprt::unary_minus() const
{
  if(is_single_value_interval())
  {
    handle_constants(unary_minus_exprt());
  }

  exprt lower;
  exprt upper;

  if(is_max())
  {
    lower = min();
  }
  else
  {
    lower = simplified_expr(unary_minus_exprt(get_upper()));
  }

  if(is_min())
  {
    upper = max();
  }
  else
  {
    upper = simplified_expr(unary_minus_exprt(get_lower()));
  }

  return constant_interval_exprt(lower, upper);
}

const constant_interval_exprt
constant_interval_exprt::plus(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, plus_exprt());
  }

  exprt lower = min();
  exprt upper = max();

  if(is_max(get_upper()) || is_max(o.get_upper()))
  {
    upper = max_exprt(type());
  }
  else
  {
    assert(!is_max(get_upper()) && !is_max(o.get_upper()));
    upper = simplified_expr(plus_exprt(get_upper(), o.get_upper()));
  }

  if(is_min(get_lower()) || is_min(o.get_lower()))
  {
    lower = min_exprt(type());
  }
  else
  {
    assert(!is_min(get_lower()) && !is_min(o.get_lower()));
    lower = simplified_expr(plus_exprt(get_lower(), o.get_lower()));
  }

  return simplified_interval(lower, upper);
}

const constant_interval_exprt
constant_interval_exprt::minus(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, minus_exprt());
  }

  // e.g. [t.u - o.l, t.l - o.u]
  return plus(o.unary_minus().swap());
}

const constant_interval_exprt
constant_interval_exprt::multiply(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, mult_exprt());
  }

  mult_exprt operation;
  operation.type() = type();
  return get_extremes(*this, o, operation);
}

const constant_interval_exprt
constant_interval_exprt::divide(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, div_exprt());
  }

  // If other might be division by zero, set everything to top.
  if(o.contains_zero())
  {
    return top();
  }

  div_exprt operation;
  return get_extremes(*this, o, operation);
}

const constant_interval_exprt
constant_interval_exprt::modulo(const constant_interval_exprt &o) const
{
  // SEE https://stackoverflow.com/questions/11720656/modulo-operation-with-negative-numbers

  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, mod_exprt());
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
    assert(contains_zero());

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

const tvt constant_interval_exprt::is_true() const
{
  // tvt not
  return !is_false();
}

const tvt constant_interval_exprt::is_false() const
{
  if(equal(constant_interval_exprt(zero())).is_true())
  {
    return tvt(true);
  }

  if(contains(constant_interval_exprt(zero())))
  {
    assert(is_positive(get_upper()) || is_negative(get_lower()));
    return tvt::unknown();
  }

  return tvt(false);
}

const tvt
constant_interval_exprt::logical_or(const constant_interval_exprt &o) const
{
  tvt a = is_true();
  tvt b = o.is_true();

  return (a || b);
}

const tvt
constant_interval_exprt::logical_and(const constant_interval_exprt &o) const
{
  return (is_true() && o.is_true());
}

const tvt
constant_interval_exprt::logical_xor(const constant_interval_exprt &o) const
{
  return ((is_true() && !o.is_true()) || (!is_true() && o.is_true()));
}

const tvt constant_interval_exprt::logical_not() const
{
  if(is_true().is_true())
  {
    return tvt(false);
  }

  if(is_false().is_true())
  {
    return tvt(true);
  }

  return tvt::unknown();
}

const constant_interval_exprt
constant_interval_exprt::left_shift(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, shl_exprt());
  }

  if(is_negative(o.get_lower()))
  {
    return top();
  }

  shl_exprt operation;
  operation.type() = type();
  return get_extremes(*this, o, operation);
}

// Arithmetic
const constant_interval_exprt
constant_interval_exprt::right_shift(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, ashr_exprt());
  }

  if(is_negative(o.get_lower()))
  {
    return top();
  }

  ashr_exprt operation;
  operation.type() = type();
  return get_extremes(*this, o, operation);
}

const constant_interval_exprt
constant_interval_exprt::bitwise_xor(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, bitxor_exprt());
  }

  return top();
}

const constant_interval_exprt
constant_interval_exprt::bitwise_or(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, bitor_exprt());
  }

  return top();
}

const constant_interval_exprt
constant_interval_exprt::bitwise_and(const constant_interval_exprt &o) const
{
  if(o.is_single_value_interval() && is_single_value_interval())
  {
    handle_constants(o, bitand_exprt());
  }

  return top();
}

const constant_interval_exprt constant_interval_exprt::bitwise_not() const
{
  if(is_single_value_interval())
  {
    handle_constants(bitnot_exprt());
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

  if(equal(get_upper(), o.get_upper()) && equal(get_upper(), o.get_upper()))
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

const constant_interval_exprt constant_interval_exprt::increment() const
{
  return plus(constant_interval_exprt(from_integer(mp_integer(1), type())));
}

const constant_interval_exprt constant_interval_exprt::decrement() const
{
  return minus(constant_interval_exprt(from_integer(mp_integer(1), type())));
}

const constant_interval_exprt constant_interval_exprt::get_extremes(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b,
  const exprt operation)
{
  constant_interval_exprt result;

  std::vector<exprt> results;

  results.push_back(
    generate_expression(a.get_lower(), b.get_lower(), operation));
  results.push_back(
    generate_expression(a.get_lower(), b.get_upper(), operation));
  results.push_back(
    generate_expression(a.get_upper(), b.get_lower(), operation));
  results.push_back(
    generate_expression(a.get_upper(), b.get_upper(), operation));

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

  assert(0);
}

exprt constant_interval_exprt::generate_expression(
  const exprt &a,
  const exprt &b,
  const exprt &operation)
{
  if(operation.id() == ID_mult)
  {
    return generate_multiply_expression(a, b, operation);
  }

  if(operation.id() == ID_div)
  {
    return generate_division_expression(a, b, operation);
  }

  if(operation.id() == ID_mod)
  {
    return generate_modulo_expression(a, b, operation);
  }

  if(operation.id() == ID_shl || operation.id() == ID_ashr)
  {
    return generate_shift_expression(a, b, operation);
  }

  assert(0 && "Not yet implemented!");
}

exprt constant_interval_exprt::generate_multiply_expression(
  const exprt &a,
  const exprt &b,
  exprt operation)
{
  assert(operation.id() == ID_mult);
  assert(operation.type().is_not_nil() && is_numeric(operation.type()));

  if(is_max(a))
  {
    return generate_multiply_expression_max(b);
  }

  if(is_max(b))
  {
    return generate_multiply_expression_max(a);
  }

  if(is_min(a))
  {
    return generate_multiply_expression_min(a, b);
  }

  if(is_min(b))
  {
    return generate_multiply_expression_min(b, a);
  }

  assert(!is_extreme(a) && !is_extreme(b));

  operation.copy_to_operands(a, b);
  return simplified_expr(operation);
}

exprt constant_interval_exprt::generate_multiply_expression_max(
  const exprt &expr)
{
  if(is_max(expr))
  {
    return max_exprt(expr);
  }

  if(is_min(expr))
  {
    if(is_negative(expr))
    {
      return min_exprt(expr);
    }
    else
    {
      assert(!is_positive(expr) && "Min value cannot be >0.");
      assert(is_zero(expr) && "Non-negative MIN must be zero.");

      return expr;
    }
  }

  assert(!is_extreme(expr));

  if(is_negative(expr))
  {
    return min_exprt(expr);
  }

  if(is_zero(expr))
  {
    return expr;
  }

  if(is_positive(expr))
  {
    return max_exprt(expr);
  }

  assert(0 && "Unreachable.");
  return nil_exprt();
}

exprt constant_interval_exprt::generate_multiply_expression_min(
  const exprt &min,
  const exprt &other)
{
  assert(is_min(min));

  if(is_max(other))
  {
    if(is_negative(min))
    {
      return min_exprt(min);
    }
    else
    {
      assert(!is_positive(min) && "Min value cannot be >0.");
      assert(is_zero(min) && "Non-negative MIN must be zero.");

      return min;
    }
  }

  if(is_min(other))
  {
    assert(
      !is_positive(min) && !is_positive(other) && "Min value cannot be >0.");
    assert(is_negative(other) || is_zero(other));

    if(is_negative(min) && is_negative(other))
    {
      return max_exprt(min);
    }

    assert(is_zero(min) || is_zero(other));
    return (is_zero(min) ? min : other);
  }

  assert(0 && "Unreachable.");
  return nil_exprt();
}

exprt constant_interval_exprt::generate_division_expression(
  const exprt &a,
  const exprt &b,
  exprt operation)
{
  assert(operation.id() == ID_div);
  assert(operation.type().is_not_nil() && is_numeric(operation.type()));

  assert(!is_zero(b));

  if(b.is_one())
  {
    return a;
  }

  if(is_max(a))
  {
    if(is_negative(b))
    {
      return min_exprt(a);
    }

    return a;
  }

  if(is_min(a))
  {
    if(is_negative(b))
    {
      return max_exprt(a);
    }

    return a;
  }

  assert(!is_extreme(a));

  if(is_max(b))
  {
    return zero(b);
  }

  if(is_min(b))
  {
    assert(is_signed(b));
    return zero(b);
  }

  assert(!is_extreme(a) && !is_extreme(b));

  assert(!operation.has_operands());
  operation.copy_to_operands(a, b);
  return simplified_expr(operation);
}

exprt constant_interval_exprt::generate_modulo_expression(
  const exprt &a,
  const exprt &b,
  exprt operation)
{
  assert(operation.id() == ID_mod);
  assert(operation.type().is_not_nil() && is_numeric(operation.type()));

  assert(!is_zero(b));

  if(b.is_one())
  {
    return a;
  }

  if(is_max(a))
  {
    if(is_negative(b))
    {
      return min_exprt(a);
    }

    return a;
  }

  if(is_min(a))
  {
    if(is_negative(b))
    {
      return max_exprt(a);
    }

    return a;
  }

  assert(!is_extreme(a));

  if(is_max(b))
  {
    return zero(b);
  }

  if(is_min(b))
  {
    assert(is_signed(b));
    return zero(b);
  }

  assert(!is_extreme(a) && !is_extreme(b));

  assert(!operation.has_operands());
  operation.copy_to_operands(a, b);
  return simplified_expr(operation);
}

const constant_interval_exprt constant_interval_exprt::eval(const exprt &expr)
{
  const irep_idt &id = expr.id();

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
    //return logical_not();
    return top();
  }

  return top();
}

const constant_interval_exprt constant_interval_exprt::eval(
  const exprt &expr,
  const constant_interval_exprt &o)
{
  const irep_idt &id = expr.id();

  if(id == ID_plus)
  {
    return plus(o);
  }
  if(id == ID_minus)
  {
    return unary_minus(o);
  }
  if(id == ID_mult)
  {
    return multiply(o);
  }
  if(id == ID_div)
  {
    return divide(o);
  }
  if(id == ID_mod)
  {
    return modulo(o);
  }
  if(id == ID_shl)
  {
    return left_shift(o);
  }
  if(id == ID_ashr)
  {
    return right_shift(o);
  }
  if(id == ID_bitor)
  {
    return bitwise_or(o);
  }
  if(id == ID_bitand)
  {
    return bitwise_and(o);
  }
  if(id == ID_bitxor)
  {
    return bitwise_xor(o);
  }
  if(id == ID_lt)
  {
    return tv_to_interval(less_than(o));
  }
  if(id == ID_le)
  {
    return tv_to_interval(less_than_or_equal(o));
  }
  if(id == ID_gt)
  {
    return tv_to_interval(greater_than(o));
  }
  if(id == ID_ge)
  {
    return tv_to_interval(greater_than_or_equal(o));
  }
  if(id == ID_equal)
  {
    return tv_to_interval(equal(o));
  }
  if(id == ID_notequal)
  {
    return tv_to_interval(not_equal(o));
  }
  if(id == ID_and)
  {
    return tv_to_interval(logical_and(o));
  }
  if(id == ID_or)
  {
    return tv_to_interval(logical_or(o));
  }
  if(id == ID_xor)
  {
    return tv_to_interval(logical_xor(o));
  }

  return top();
}

const constant_interval_exprt
constant_interval_exprt::tv_to_interval(const tvt &tv) const
{
  if(tv.is_true())
  {
    return constant_interval_exprt(from_integer(1, type()));
  }
  if(tv.is_false())
  {
    return constant_interval_exprt(zero());
  }

  assert(tv.is_unknown());
  return top();
}

exprt constant_interval_exprt::generate_shift_expression(
  const exprt &a,
  const exprt &b,
  exprt operation)
{
  assert(operation.id() == ID_shl || operation.id() == ID_ashr);

  if(is_zero(a) || is_zero(b))
  {
    // Shifting zero does nothing.
    // Shifting BY zero also does nothing.
    return a;
  }

  // Should be caught at an earlier stage.
  assert(!is_negative(b));

  if(is_max(a))
  {
    return a;
  }

  if(is_min(a))
  {
    return a;
  }

  if(is_max(b))
  {
    return min_exprt(b);
  }

  assert(!is_extreme(a) && !is_extreme(b));

  operation.op0() = a;
  operation.op1() = b;
  return simplified_expr(operation);
}

const constant_interval_exprt
constant_interval_exprt::handle_constants(exprt expr) const
{
  if(is_single_value_interval())
  {
    expr.type() = type();
    expr.copy_to_operands(get_lower());

    return constant_interval_exprt(simplified_expr(expr));
  }

  return top();
}

const constant_interval_exprt constant_interval_exprt::handle_constants(
  const constant_interval_exprt &o,
  exprt expr) const
{
  if(is_single_value_interval() && o.is_single_value_interval())
  {
    expr.type() = type();
    expr.copy_to_operands(get_lower(), o.get_lower());
    return constant_interval_exprt(simplified_expr(expr));
  }

  return top();
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
const constant_interval_exprt
constant_interval_exprt::simplified_interval(exprt &l, exprt &r)
{
  return constant_interval_exprt(simplified_expr(l), simplified_expr(r));
}

exprt constant_interval_exprt::simplified_expr(exprt expr)
{
  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  assert(!contains_extreme(expr));

  return simplify_expr(expr, ns);
}

constant_exprt constant_interval_exprt::zero(const typet &type)
{
  constant_exprt zero = from_integer(mp_integer(0), type);
  assert(zero.is_zero()); // NOT is_zero(zero) (inf. recursion
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
  return (is_min() && is_max());
}

bool constant_interval_exprt::is_bottom() const
{
  // This should ONLY happen for bottom.
  return is_min(get_upper()) || is_max(get_lower());
}

const constant_interval_exprt constant_interval_exprt::top(const typet &type)
{
  return constant_interval_exprt(type);
}

const constant_interval_exprt constant_interval_exprt::bottom(const typet &type)
{
  return constant_interval_exprt(max_exprt(type), min_exprt(type));
}

const constant_interval_exprt constant_interval_exprt::top() const
{
  return constant_interval_exprt(type());
}

const constant_interval_exprt constant_interval_exprt::bottom() const
{
  return bottom(type());
}

const constant_interval_exprt
constant_interval_exprt::swap(constant_interval_exprt &i)
{
  return constant_interval_exprt(i.get_upper(), i.get_lower());
}

const constant_interval_exprt constant_interval_exprt::swap() const
{
  return constant_interval_exprt(get_lower(), get_upper());
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
         t.id() == ID_pointer || t.id() == ID_bool;
}

bool constant_interval_exprt::is_signed(const typet &t)
{
  return t.id() == ID_signedbv;
}

bool constant_interval_exprt::is_unsigned(const typet &t)
{
  return t.id() == ID_bv || t.id() == ID_unsignedbv || t.id() == ID_pointer ||
         t.id() == ID_bool;
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

bool constant_interval_exprt::is_max() const
{
  return is_max(get_upper());
}

bool constant_interval_exprt::is_min() const
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

  assert(is_signed(expr));
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

  assert(!is_max(expr) && !is_min(expr));

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

  assert(is_signed(expr));

  if(is_min(expr))
  {
    return true;
  }

  assert(!is_extreme(expr));

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
    // Best we can do now is a==b?, but this is covered by the above, so always false.
    assert(!(a == b));
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

  assert(!is_extreme(l, r));

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

  assert(!is_max(l));

  if(is_min(r))
  {
    // Can't be smaller than min.
    return false;
  }

  assert(!is_max(l) && !is_min(r));

  if(is_min(l))
  {
    assert(!is_min(r));
    return true;
  }

  assert(!is_max(l) && !is_min(r) && !is_min(l));

  if(is_max(r))
  {
    // If r is max, then l is less, unless l is max.
    return !is_max(l);
  }

  assert(!is_max(l) && !is_min(r) && !is_min(l) && !is_max(r));

  assert(!is_extreme(l, r));

  return simplified_expr(binary_relation_exprt(l, ID_lt, r)).is_true();
}

bool constant_interval_exprt::greater_than(const exprt &a, const exprt &b)
{
  return less_than(b, a);

  //  if(!is_numeric(a) || !is_numeric(b))
  //  {
  //    return false;
  //  }
  //
  //  exprt l=(is_min(a) && is_unsigned(a)) ? zero(a) : a;
  //  exprt r=(is_min(b) && is_unsigned(b)) ? zero(b) : b;
  //
  //  if(is_max(l) && !is_max(r))
  //  {
  //    return true;
  //  }
  //
  //  if((is_max(l) && is_max(r)) || (is_min(l) && is_min(r)))
  //  {
  //    return false;
  //  }
  //
  //  if(is_min(l) && is_max(r))
  //  {
  //    return false;
  //  }
  //
  //  assert(!is_extreme(l) && !is_extreme(r));
  //
  //  return simplified_expr(binary_relation_exprt(l, ID_gt, r)).is_true();
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

  out << dstringt("[");

  if(!is_min())
  {
    if(is_bitvector(get_lower()))
    {
      out << binary2integer(get_lower().get(ID_value).c_str(), 2);
    }
    else
    {
      out << get_lower().get(ID_value);
    }
  }
  else
  {
    if(is_signed(get_lower()))
    {
      out << dstringt("MIN");
    }
    else
    {
      out << dstringt("0");
    }
  }

  out << dstringt(",");

  if(!is_max())
  {
    if(is_bitvector(get_upper()))
    {
      out << binary2integer(get_upper().get(ID_value).c_str(), 2);
    }
    else
    {
      out << get_upper().get(ID_value);
    }
  }
  else
    out << dstringt("MAX");

  out << dstringt("]");

  return out.str();
}

std::ostream &operator<<(std::ostream &out, const constant_interval_exprt &i)
{
  out << i.to_string();

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

const constant_interval_exprt
constant_interval_exprt::unary_plus(const constant_interval_exprt &a)
{
  return a.unary_plus();
}

const constant_interval_exprt
constant_interval_exprt::unary_minus(const constant_interval_exprt &a)
{
  return a.unary_minus();
}

/* Binary */
const constant_interval_exprt constant_interval_exprt::plus(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.plus(b);
}

const constant_interval_exprt constant_interval_exprt::minus(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.minus(b);
}

const constant_interval_exprt constant_interval_exprt::multiply(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.multiply(b);
}

const constant_interval_exprt constant_interval_exprt::divide(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.divide(b);
}

const constant_interval_exprt constant_interval_exprt::modulo(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.modulo(b);
}

/* Binary shifts */
const constant_interval_exprt constant_interval_exprt::left_shift(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.left_shift(b);
}

const constant_interval_exprt constant_interval_exprt::right_shift(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.right_shift(b);
}

/* Unary bitwise */
const constant_interval_exprt
constant_interval_exprt::bitwise_not(const constant_interval_exprt &a)
{
  return a.bitwise_not();
}

/* Binary bitwise */
const constant_interval_exprt constant_interval_exprt::bitwise_xor(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.bitwise_xor(b);
}

const constant_interval_exprt constant_interval_exprt::bitwise_or(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.bitwise_or(b);
}

const constant_interval_exprt constant_interval_exprt::bitwise_and(
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

const constant_interval_exprt
constant_interval_exprt::increment(const constant_interval_exprt &a)
{
  return a.increment();
}

const constant_interval_exprt
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
  return a.is_min();
}

bool constant_interval_exprt::is_max(const constant_interval_exprt &a)
{
  return a.is_max();
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

const constant_interval_exprt
tv_to_interval(const constant_interval_exprt &interval, const tvt &tv)
{
  return interval.tv_to_interval(tv);
}

const tvt constant_interval_exprt::is_true(const constant_interval_exprt &a)
{
  return a.is_true();
}

const tvt constant_interval_exprt::is_false(const constant_interval_exprt &a)
{
  return a.is_false();
}

const tvt constant_interval_exprt::logical_and(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.logical_and(b);
}

const tvt constant_interval_exprt::logical_or(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.logical_or(b);
}

const tvt constant_interval_exprt::logical_xor(
  const constant_interval_exprt &a,
  const constant_interval_exprt &b)
{
  return a.logical_xor(b);
}

const tvt constant_interval_exprt::logical_not(const constant_interval_exprt &a)
{
  return a.logical_not();
}
