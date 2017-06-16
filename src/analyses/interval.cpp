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

#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <ostream>
#include <sstream>


//make clean -s && make -j 7 CXX="/usr/local/bin/ccache g++" -s && ./unit_tests

const intervalt intervalt::unary_plus() const
{
  return *this;
}

const intervalt intervalt::unary_minus() const
{
  if(is_constant())
  {
    handle_constants(unary_minus_exprt());
  }

  exprt lower;
  exprt upper;

  if(is_max())
  {
    lower=min();
  }
  else
  {
    lower = simplified_expr(unary_minus_exprt(get_upper()));
  }

  if(is_min())
  {
    upper=max();
  }
  else
  {
    upper = simplified_expr(unary_minus_exprt(get_lower()));
  }

  return intervalt(lower, upper);
}

const intervalt intervalt::plus(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
  {
    handle_constants(o, plus_exprt());
  }

  exprt lower = min();
  exprt upper = max();

  if(is_max(get_upper()) || is_max(o.get_upper()))
  {
    upper = max_exprt(get_type());
  }
  else
  {
    assert(!is_max(get_upper()) && !is_max(o.get_upper()));
    upper = simplified_expr(plus_exprt(get_upper(), o.get_upper()));
  }

  if(is_min(get_lower()) || is_min(o.get_lower()))
  {
    lower = min_exprt(get_type());
  }
  else
  {
    assert(!is_min(get_lower()) && !is_min(o.get_lower()));
    lower = simplified_expr(plus_exprt(get_lower(), o.get_lower()));
  }

  return simplified_interval(lower, upper);
}

const intervalt intervalt::minus(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
  {
    handle_constants(o, minus_exprt());
  }

  // e.g. [t.u - o.l, t.l - o.u]
  return plus(o.unary_minus().swap());
}

const intervalt intervalt::multiply(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
  {
    handle_constants(o, mult_exprt());
  }

  mult_exprt operation;
  operation.type()=get_type();
  return get_extremes(*this, o, operation);
}

const intervalt intervalt::divide(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
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

const intervalt intervalt::modulo(const intervalt& o) const
{
  // SEE https://stackoverflow.com/questions/11720656/modulo-operation-with-negative-numbers

  if(o.is_constant() && is_constant())
  {
    handle_constants(o, mod_exprt());
  }

  if(o.is_bottom())
  {
    return top();
  }

  // If the RHS is 1, or -1 (signed only), then return zero.
  if(o == intervalt(from_integer(1, o.get_type())) ||
      (o.is_signed() && o == intervalt(from_integer(-1, o.get_type()))))
  {
    return intervalt(zero());
  }

  // If other might be modulo by zero, set everything to top.
  if(o.contains_zero())
  {
    return top();
  }

  if(is_zero())
  {
    return intervalt(zero());
  }

  exprt lower=min();
  exprt upper=max();

  // Positive case (cannot have zero on RHS).
  // 10 % 5 = [0, 4], 3 % 5 = [0, 3]
  if(!is_negative() && o.is_positive())
  {
    lower=zero();
    upper=get_min(get_upper(), o.decrement().get_upper());
  }

  // [-5, 5] % [3]
  if(is_negative(get_lower()) && is_positive(get_upper()))
  {
    assert(contains_zero());

    // This can be done more accurately.
    lower=get_min(o.get_lower(), get_lower());
    upper=get_max(o.get_upper(), get_upper());
  }

  if(is_negative() && o.is_negative())
  {
    lower=get_min(o.get_lower(), o.get_lower());
    upper=zero();
  }

  return intervalt(lower, upper);
}


const tvt intervalt::is_true() const
{
  // tvt not
  return !is_false();
}

const tvt intervalt::is_false() const
{
  if(equal(intervalt(zero())).is_true())
  {
    return tvt(true);
  }

  if(contains(intervalt(zero())))
  {
    assert(is_positive(get_upper()) || is_negative(get_lower()));
    return tvt::unknown();
  }

  return tvt(false);
}

const tvt intervalt::logical_or(const intervalt& o) const
{
  tvt a = is_true();
  tvt b = o.is_true();

  return (a || b);
}

const tvt intervalt::logical_and(const intervalt& o) const
{
  return (is_true() && o.is_true());
}

const tvt intervalt::logical_xor(const intervalt& o) const
{
  return (
      (is_true() && !o.is_true()) ||
      (!is_true() && o.is_true())
  );
}

const tvt intervalt::logical_not() const
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


const intervalt intervalt::left_shift(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
  {
    handle_constants(o, shl_exprt());
  }

  if(is_negative(o.get_lower()))
  {
    return top();
  }

  shl_exprt operation;
  operation.type()=get_type();
  return get_extremes(*this, o, operation);
}

// Arithmetic
const intervalt intervalt::right_shift(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
  {
    handle_constants(o, ashr_exprt());
  }

  if(is_negative(o.get_lower()))
  {
    return top();
  }

  ashr_exprt operation;
  operation.type()=get_type();
  return get_extremes(*this, o, operation);
}

const intervalt intervalt::bitwise_xor(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
  {
    handle_constants(o, bitxor_exprt());
  }

  return top();
}

const intervalt intervalt::bitwise_or(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
  {
    handle_constants(o, bitor_exprt());
  }

  return top();
}

const intervalt intervalt::bitwise_and(const intervalt& o) const
{
  if(o.is_constant() && is_constant())
  {
    handle_constants(o, bitand_exprt());
  }

  return top();
}

const intervalt intervalt::bitwise_not() const
{
  if(is_constant())
  {
    handle_constants(bitnot_exprt());
  }

  return top();
}

tvt intervalt::less_than(const intervalt &o) const
{
  // [get_lower, get_upper] < [o.get_lower(), o.get_upper()]
  if(is_constant() && o.is_constant())
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

tvt intervalt::greater_than(const intervalt& o) const
{
  return o.less_than(*this);
}

tvt intervalt::less_than_or_equal(const intervalt& o) const
{
  if(is_constant() && o.is_constant())
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

tvt intervalt::greater_than_or_equal(const intervalt& o) const
{
  return o.less_than_or_equal(*this);
}

tvt intervalt::equal(const intervalt& o) const
{
  if(is_constant() && o.is_constant())
  {
    return tvt(equal(get_lower(), o.get_lower()));
  }

  if(equal(get_upper(), o.get_upper()) && equal(get_upper(), o.get_upper()))
  {
    return tvt(true);
  }

  if(less_than(o).is_true() || greater_than(o).is_true() || o.less_than(*this).is_true() || o.greater_than(*this).is_true())
  {
    return tvt(false);
  }

  // Don't know.  Could have [3, 5] == [4] (not equal)
  return tvt::unknown();
}

tvt intervalt::not_equal(const intervalt& o) const
{
  return !equal(o);
}

const intervalt intervalt::increment() const
{
  return plus(intervalt(from_integer(mp_integer(1), get_type())));

}

const intervalt intervalt::decrement() const
{
  return minus(intervalt(from_integer(mp_integer(1), get_type())));
}

const intervalt intervalt::get_extremes(
    const intervalt &a,
    const intervalt &b,
    const exprt operation)
{
  intervalt result;

  std::vector<exprt> results;

  results.push_back(
      generate_expression(a.get_lower(), b.get_lower(), operation));
  results.push_back(
      generate_expression(a.get_lower(), b.get_upper(), operation));
  results.push_back(
      generate_expression(a.get_upper(), b.get_lower(), operation));
  results.push_back(
      generate_expression(a.get_upper(), b.get_upper(), operation));


  for(auto result: results)
  {
    if(!is_extreme(result) && contains_extreme(result))
    {
      return intervalt(result.type());
    }
  }

  exprt min=get_min(results);
  exprt max=get_max(results);

  return simplified_interval(min, max);
}

exprt intervalt::get_extreme(std::vector<exprt> values, bool min_value)
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

  typet type=values.begin()->type();

  for(auto v: values)
  {
    if((min_value && is_min(v)) || (!min_value && is_max(v)))
    {
      return v;
    }
  }

  for(auto left: values)
  {
    bool all_left_OP_right = true;

    for(auto right: values)
    {
      if((min_value && less_than_or_equal(left, right)) || (!min_value && greater_than_or_equal(left, right)))
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



exprt intervalt::generate_expression(const exprt& a, const exprt& b, const exprt &operation)
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

exprt intervalt::generate_multiply_expression(const exprt& a, const exprt& b,
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


exprt intervalt::generate_multiply_expression_max(const exprt &expr)
{
  if(is_max (expr))
  {
    return max_exprt(expr);
  }

  if(is_min (expr))
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

  if(is_negative (expr))
  {
    return min_exprt(expr);
  }

  if(is_zero (expr))
  {
    return expr;
  }

  if(is_positive (expr))
  {
    return max_exprt(expr);
  }

  assert(0 && "Unreachable.");
  return nil_exprt();
}

exprt intervalt::generate_multiply_expression_min(const exprt &min, const exprt &other)
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
    assert(!is_positive(min) && !is_positive(other)  && "Min value cannot be >0.");
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



exprt intervalt::generate_division_expression(const exprt& a, const exprt& b,
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

exprt intervalt::generate_modulo_expression(const exprt& a, const exprt& b,
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

const intervalt intervalt::eval(const exprt& expr)
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
    return logical_not();
  }

  return top();
}

const intervalt intervalt::eval(const exprt& expr, const intervalt& o)
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

const intervalt intervalt::tv_to_interval(const tvt &tv) const
{
  if(tv.is_true())
  {
    return intervalt(from_integer(1, get_type()));
  }
  if(tv.is_false())
  {
    return intervalt(zero());
  }

  assert(tv.is_unknown());
  return top();
}

exprt intervalt::generate_shift_expression(const exprt& a, const exprt& b,
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

  operation.op0()=a;
  operation.op1()=b;
  return simplified_expr(operation);
}
