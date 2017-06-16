#include "interval.h"

#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/arith_tools.h>
#include <ostream>
#include <sstream>

const exprt& intervalt::get_lower() const
{
  return lower;
}

const exprt& intervalt::get_upper() const
{
  return upper;
}

const typet& intervalt::get_type() const
{
  return type;
}

const intervalt intervalt::handle_constants(exprt expr) const
{
  if(is_constant())
  {
    expr.type()=get_type();
    expr.copy_to_operands(get_lower());

    return intervalt(simplified_expr(expr));
  }

  return top();
}

const intervalt intervalt::handle_constants(const intervalt &o, exprt expr) const
{
  if(is_constant() && o.is_constant())
  {
    expr.type()=get_type();
    expr.copy_to_operands(get_lower(), o.get_lower());
    return intervalt(simplified_expr(expr));
  }

  return top();
}

exprt intervalt::get_max(const exprt &a, const exprt &b)
{
  return greater_than(a, b) ? a : b;
}

exprt intervalt::get_min(const exprt &a, const exprt &b)
{
  return less_than(a, b) ? a : b;
}

exprt intervalt::get_min(std::vector<exprt> &values)
{
  return get_extreme(values, true);
}

exprt intervalt::get_max(std::vector<exprt> &values)
{
  return get_extreme(values, false);
}

/* we don't simplify in the constructor otherwise */
const intervalt intervalt::simplified_interval(exprt &l, exprt &r)
{
  return intervalt(simplified_expr(l), simplified_expr(r));
}

exprt intervalt::simplified_expr(exprt expr)
{
  symbol_tablet symbol_table;
  const namespacet ns(symbol_table);

  assert(!contains_extreme(expr));

  return simplify_expr(expr, ns);
}

/* Don't allow different types in upper and lower */
const typet& intervalt::calculate_type(const exprt &l, const exprt &u) const
{
  if(u.type() != l.type())
  {
    assert(0 && "Cannot support mixed types.");
  }

  assert(u.type() == l.type());
  return u.type();
}


constant_exprt intervalt::zero(const typet& type)
{
  constant_exprt zero = from_integer(mp_integer(0), type);
  assert(zero.is_zero()); // NOT is_zero(zero) (inf. recursion
  return zero;
}

constant_exprt intervalt::zero(const exprt& expr)
{
  return zero(expr.type());
}

constant_exprt intervalt::zero(const intervalt &interval)
{
  return zero(interval.get_type());
}

constant_exprt intervalt::zero() const
{
  return zero(get_type());
}

min_exprt intervalt::min() const
{
  return min_exprt(get_type());
}

max_exprt intervalt::max() const
{
  return max_exprt(get_type());
}

bool intervalt::is_top() const
{
  return (is_min() && is_max());
}

bool intervalt::is_bottom() const
{
  // This should ONLY happen for bottom.
  return is_min(get_upper()) || is_max(get_lower());
}

const intervalt intervalt::top(const typet &type)
{
  return intervalt(type);
}

const intervalt intervalt::bottom(const typet &type)
{
  return intervalt(max_exprt(type), min_exprt(type));
}

const intervalt intervalt::top() const
{
  return intervalt(get_type());
}

const intervalt intervalt::bottom() const
{
  return bottom(type);
}

const intervalt intervalt::swap(intervalt &i)
{
  return intervalt(i.get_upper(), i.get_lower());
}

const intervalt intervalt::swap() const
{
  return intervalt(get_lower(), get_upper());
}

/* Helpers */

bool intervalt::is_int() const
{
  return is_int(get_type());
}

bool intervalt::is_float() const
{
  return is_float(get_type());
}

bool intervalt::is_numeric(const typet &type)
{
  return is_int(type) || is_float(type);
}

bool intervalt::is_numeric() const
{
  return is_numeric(get_type());
}

bool intervalt::is_numeric(const exprt &expr)
{
  return is_numeric(expr.type());
}

bool intervalt::is_numeric(const intervalt &interval)
{
  return interval.is_numeric();
}

bool intervalt::is_int(const typet &type)
{
  return (is_signed(type) || is_unsigned(type));
}

bool intervalt::is_float(const typet &src)
{
  return src.id() == ID_floatbv;
}

bool intervalt::is_int(const exprt &expr)
{
  return is_int(expr.type());
}

bool intervalt::is_int(const intervalt &interval)
{
  return interval.is_int();
}

bool intervalt::is_float(const exprt &expr)
{
  return is_float(expr.type());
}

bool intervalt::is_float(const intervalt &interval)
{
  return interval.is_float();
}


bool intervalt::is_bitvector(const typet &t)
{
  return t.id() == ID_bv || t.id() == ID_signedbv || t.id() == ID_unsignedbv
      || t.id() == ID_pointer || t.id() == ID_bool;
}

bool intervalt::is_signed(const typet &t)
{
  return t.id() == ID_signedbv;
}

bool intervalt::is_unsigned(const typet &t)
{
  return t.id() == ID_bv || t.id() == ID_unsignedbv || t.id() == ID_pointer
      || t.id() == ID_bool;
}

bool intervalt::is_signed(const intervalt &interval)
{
  return is_signed(interval.get_type());
}

bool intervalt::is_unsigned(const intervalt &interval)
{
  return is_unsigned(interval.get_type());
}

bool intervalt::is_bitvector(const intervalt &interval)
{
  return is_bitvector(interval.get_type());
}

bool intervalt::is_signed(const exprt &expr)
{
  return is_signed(expr.type());
}

bool intervalt::is_unsigned(const exprt &expr)
{
  return is_unsigned(expr.type());
}

bool intervalt::is_bitvector(const exprt &expr)
{
  return is_bitvector(expr.type());
}

bool intervalt::is_signed() const
{
  return is_signed(get_type());
}

bool intervalt::is_unsigned() const
{
  return is_unsigned(get_type());
}

bool intervalt::is_bitvector() const
{
  return is_bitvector(get_type());
}

bool intervalt::is_extreme(const exprt &expr)
{
  return (is_max(expr) || is_min(expr));
}

bool intervalt::is_extreme(const exprt &expr1, const exprt &expr2)
{
  return is_extreme(expr1) || is_extreme(expr2);
}

bool intervalt::is_max() const
{
  return is_max(get_upper());
}

bool intervalt::is_min() const
{
  return is_min(get_lower());
}

bool intervalt::is_max(const exprt &expr)
{
  return expr.id() == ID_max;
}

bool intervalt::is_min(const exprt &expr)
{
  return expr.id() == ID_min;
}

bool intervalt::is_positive(const exprt &expr)
{
  exprt simplified=simplified_expr(expr);

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

bool intervalt::is_zero(const exprt &expr)
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

bool intervalt::is_negative(const exprt &expr)
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

exprt intervalt::abs(const exprt &expr)
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


bool intervalt::equal(const exprt& a, const exprt& b)
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

  exprt l=(is_min(a) && is_unsigned(a)) ? zero(a) : a;
  exprt r=(is_min(b) && is_unsigned(b)) ? zero(b) : b;

  // CANNOT use is_zero(X) but can use X.is_zero();
  if((is_min(l) && is_min(r)))
  {
    return true;
  }

  if((is_max(l) && !is_max(r)) || (is_min(l) && !is_min(r)) ||
     (is_max(r) && !is_max(l)) || (is_min(r) && !is_min(l)))
  {
    return false;
  }

  assert(!is_extreme(l, r));

  return simplified_expr(equal_exprt(l, r)).is_true();
}

// TODO: Signed/unsigned comparisons.
bool intervalt::less_than(const exprt& a, const exprt& b)
{
  if(!is_numeric(a) || !is_numeric(b))
  {
    return false;
  }

  exprt l=(is_min(a) && is_unsigned(a)) ? zero(a) : a;
  exprt r=(is_min(b) && is_unsigned(b)) ? zero(b) : b;

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

bool intervalt::greater_than(const exprt &a, const exprt &b)
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

bool intervalt::less_than_or_equal(const exprt& a, const exprt& b)
{
  return less_than(a, b) || equal(a, b);
}

bool intervalt::greater_than_or_equal(const exprt& a, const exprt& b)
{
  return greater_than(a, b) || equal(a, b);
}

bool intervalt::not_equal(const exprt &a, const exprt &b)
{
  return !equal(a, b);
}

bool intervalt::contains(const intervalt& interval) const
{
  // [a, b] Contains [c, d] If c >= a and d <= b.
  return(
      less_than_or_equal(interval.get_upper(), get_upper())
      &&
      greater_than_or_equal(interval.get_lower(), get_lower())
  );
}


std::string intervalt::to_string() const
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

std::ostream& operator <<(std::ostream& out,
    const intervalt& i)
{
  out << i.to_string();

  return out;
}

bool operator< (const intervalt &lhs, const intervalt &rhs)
{
  return lhs.less_than(rhs).is_true();
}

bool operator> (const intervalt &lhs, const intervalt &rhs)
{
  return lhs.greater_than(rhs).is_true();
}

bool operator<=(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.less_than_or_equal(rhs).is_true();
}

bool operator>=(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.greater_than(rhs).is_true();
}

bool operator==(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.equal(rhs).is_true();
}

bool operator!=(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.not_equal(rhs).is_true();
}

const intervalt operator+(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.unary_plus(rhs);
}

const intervalt operator-(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.minus(rhs);
}

const intervalt operator/(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.divide(rhs);
}

const intervalt operator*(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.multiply(rhs);
}

const intervalt operator%(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.modulo(rhs);
}

const intervalt operator&(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.bitwise_and(rhs);
}

const intervalt operator|(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.bitwise_or(rhs);
}

const intervalt operator^(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.bitwise_xor(rhs);
}

const intervalt operator!(const intervalt &lhs)
{
  return lhs.bitwise_not();
}

const intervalt operator<<(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.left_shift(rhs);
}

const intervalt operator>>(const intervalt &lhs, const intervalt &rhs)
{
  return lhs.right_shift(rhs);
}

const intervalt intervalt::unary_plus(const intervalt &a)
{
  return a.unary_plus();
}

const intervalt intervalt::unary_minus(const intervalt &a)
{
  return a.unary_minus();
}

/* Binary */
const intervalt intervalt::plus(const intervalt &a, const intervalt &b)
{
  return a.plus(b);
}

const intervalt intervalt::minus(const intervalt &a, const intervalt &b)
{
  return a.minus(b);
}

const intervalt intervalt::multiply(const intervalt &a, const intervalt &b)
{
  return a.multiply(b);
}

const intervalt intervalt::divide(const intervalt &a, const intervalt &b)
{
  return a.divide(b);
}

const intervalt intervalt::modulo(const intervalt &a, const intervalt &b)
{
  return a.modulo(b);
}

/* Binary shifts */
const intervalt intervalt::left_shift(const intervalt &a, const intervalt &b)
{
  return a.left_shift(b);
}

const intervalt intervalt::right_shift(const intervalt &a, const intervalt &b)
{
  return a.right_shift(b);
}

/* Unary bitwise */
const intervalt intervalt::bitwise_not(const intervalt &a)
{
  return a.bitwise_not();
}

/* Binary bitwise */
const intervalt intervalt::bitwise_xor(const intervalt &a, const intervalt &b)
{
  return a.bitwise_xor(b);
}

const intervalt intervalt::bitwise_or(const intervalt &a, const intervalt &b)
{
  return a.bitwise_or(b);
}

const intervalt intervalt::bitwise_and(const intervalt &a, const intervalt &b)
{
  return a.bitwise_and(b);
}

tvt intervalt::less_than(const intervalt &a, const intervalt &b)
{
  return a.less_than(b);
}

tvt intervalt::greater_than(const intervalt &a, const intervalt &b)
{
  return a.greater_than(b);
}

tvt intervalt::less_than_or_equal(const intervalt &a, const intervalt &b)
{
  return a.less_than_or_equal(b);
}

tvt intervalt::greater_than_or_equal(const intervalt &a, const intervalt &b)
{
  return a.greater_than_or_equal(b);
}

tvt intervalt::equal(const intervalt &a, const intervalt &b)
{
  return a.equal(b);
}

tvt intervalt::not_equal(const intervalt &a, const intervalt &b)
{
  return a.equal(b);
}

const intervalt intervalt::increment(const intervalt &a)
{
  return a.increment();
}

const intervalt intervalt::decrement(const intervalt &a)
{
  return a.decrement();
}

bool intervalt::is_empty(const intervalt &a)
{
  return a.is_empty();
}

bool intervalt::is_constant(const intervalt &a)
{
  return a.is_constant();
}

bool intervalt::is_top(const intervalt &a)
{
  return a.is_top();
}

bool intervalt::is_bottom(const intervalt &a)
{
  return a.is_bottom();
}

bool intervalt::is_min(const intervalt &a)
{
  return a.is_min();
}

bool intervalt::is_max(const intervalt &a)
{
  return a.is_max();
}

bool intervalt::contains_extreme(const exprt expr)
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

bool intervalt::contains_extreme(const exprt expr1, const exprt expr2)
{
  return contains_extreme(expr1) || contains_extreme(expr2);
}

bool intervalt::is_empty() const
{
  if(greater_than(get_lower(), get_upper()))
  {
    return false;
  }

  return true;
}

bool intervalt::is_constant() const
{
  return !is_extreme(get_lower()) && !is_extreme(get_upper()) && equal(get_lower(), get_upper());
}

bool intervalt::contains_zero() const
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

  if(less_than_or_equal(get_lower(), zero()) && greater_than_or_equal(get_upper(), zero()))
  {
    return true;
  }

  return false;
}


bool intervalt::is_positive(const intervalt& interval)
{
  return interval.is_positive();
}

bool intervalt::is_zero(const intervalt& interval)
{
  return interval.is_zero();
}

bool intervalt::is_negative(const intervalt& interval)
{
  return interval.is_negative();
}

bool intervalt::is_positive() const
{
  return is_positive(get_lower()) && is_positive(get_upper());
}

bool intervalt::is_zero() const
{
  return is_zero(get_lower()) && is_zero(get_upper());
}

bool intervalt::is_negative() const
{
  return is_negative(get_lower()) && is_negative(get_upper());
}

const intervalt tv_to_interval(const intervalt &interval, const tvt &tv)
{
  return interval.tv_to_interval(tv);
}

const tvt intervalt::is_true(const intervalt& a)
{
  return a.is_true();
}

const tvt intervalt::is_false(const intervalt& a)
{
  return a.is_false();
}

const tvt intervalt::logical_and(const intervalt& a, const intervalt& b)
{
  return a.logical_and(b);
}

const tvt intervalt::logical_or(const intervalt& a, const intervalt& b)
{
  return a.logical_or(b);
}

const tvt intervalt::logical_xor(const intervalt& a, const intervalt& b)
{
  return a.logical_xor(b);
}

const tvt intervalt::logical_not(const intervalt& a)
{
  return a.logical_not();
}
