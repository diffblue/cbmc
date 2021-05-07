/*******************************************************************\

 Module: intervals

 Author: Daniel Neville (2017)

\*******************************************************************/
#ifndef CPROVER_UTIL_INTERVAL_H
#define CPROVER_UTIL_INTERVAL_H

#include <util/std_expr.h>
#include <util/threeval.h>

#include <iostream>

/// +∞ upper bound for intervals
class max_exprt : public exprt
{
public:
  explicit max_exprt(const typet &_type) : exprt(ID_max, _type)
  {
  }

  explicit max_exprt(const exprt &_expr) : exprt(ID_max, _expr.type())
  {
  }
};

/// -∞ upper bound for intervals
class min_exprt : public exprt
{
public:
  explicit min_exprt(const typet &_type) : exprt(ID_min, _type)
  {
  }

  explicit min_exprt(const exprt &_expr) : exprt(ID_min, _expr.type())
  {
  }
};

/// Represents an interval of values.
/// Bounds should be constant expressions
/// or min_exprt for the lower bound
/// or max_exprt for the upper bound
/// Also, lower bound should always be <= upper bound
class constant_interval_exprt : public binary_exprt
{
public:
  constant_interval_exprt(
    const exprt &lower,
    const exprt &upper,
    const typet type)
    : binary_exprt(lower, ID_constant_interval, upper, type)
  {
    PRECONDITION(is_well_formed());
  }

  constant_interval_exprt(const constant_interval_exprt &x)
    : constant_interval_exprt(x.get_lower(), x.get_upper(), x.type())
  {
  }

  explicit constant_interval_exprt(const exprt &x)
    : constant_interval_exprt(x, x, x.type())
  {
  }

  explicit constant_interval_exprt(const typet &type)
    : constant_interval_exprt(min_exprt(type), max_exprt(type), type)
  {
  }

  constant_interval_exprt(const exprt &lower, const exprt &upper)
    : constant_interval_exprt(lower, upper, lower.type())
  {
  }

  bool is_well_formed() const
  {
    bool b = true;

    const typet &type = this->type();
    const exprt &lower = get_lower();
    const exprt &upper = get_upper();

    b &= is_numeric() || type.id() == ID_bool || type.is_nil();

    b &= type == lower.type();
    b &= type == upper.type();

    b &= is_valid_bound(lower);
    b &= is_valid_bound(upper);

    b &= !is_numeric() || is_bottom() || less_than_or_equal(lower, upper);

    return b;
  }

  bool is_valid_bound(const exprt &expr) const
  {
    const irep_idt &id = expr.id();

    bool b = true;

    b &= id == ID_constant || id == ID_min || id == ID_max;

    if(type().id() == ID_bool && id == ID_constant)
    {
      b &= expr == true_exprt() || expr == false_exprt();
    }

    return b;
  }

  static constant_interval_exprt tvt_to_interval(const tvt &val);

  /* Naming scheme
   *      is_[X]?  Returns bool / tvt
   *      get_[X]? Returns relevant object
   *      [X]      Generator of some object.
   *      generate_[X]  generator used for evaluation
   */

  /* Getters */
  const exprt &get_lower() const;
  const exprt &get_upper() const;

  /** SET OF ARITHMETIC OPERATORS */
  constant_interval_exprt
  handle_constant_unary_expression(const irep_idt &op) const;
  constant_interval_exprt handle_constant_binary_expression(
    const constant_interval_exprt &other,
    const irep_idt &) const;

  constant_interval_exprt eval(const irep_idt &unary_operator) const;
  constant_interval_exprt
  eval(const irep_idt &binary_operator, const constant_interval_exprt &o) const;

  /* Unary arithmetic */
  constant_interval_exprt unary_plus() const;
  constant_interval_exprt unary_minus() const;

  constant_interval_exprt typecast(const typet &type) const;

  /* Logical */
  tvt is_definitely_true() const;
  tvt is_definitely_false() const;

  tvt logical_and(const constant_interval_exprt &o) const;
  tvt logical_or(const constant_interval_exprt &o) const;
  tvt logical_xor(const constant_interval_exprt &o) const;
  tvt logical_not() const;

  /* Binary */
  constant_interval_exprt plus(const constant_interval_exprt &o) const;
  constant_interval_exprt minus(const constant_interval_exprt &other) const;
  constant_interval_exprt multiply(const constant_interval_exprt &o) const;
  constant_interval_exprt divide(const constant_interval_exprt &o) const;
  constant_interval_exprt modulo(const constant_interval_exprt &o) const;

  /* Binary shifts */
  constant_interval_exprt left_shift(const constant_interval_exprt &o) const;
  constant_interval_exprt right_shift(const constant_interval_exprt &o) const;

  /* Unary bitwise */
  constant_interval_exprt bitwise_not() const;

  /* Binary bitwise */
  constant_interval_exprt bitwise_xor(const constant_interval_exprt &o) const;
  constant_interval_exprt bitwise_or(const constant_interval_exprt &o) const;
  constant_interval_exprt bitwise_and(const constant_interval_exprt &o) const;

  tvt less_than(const constant_interval_exprt &o) const;
  tvt greater_than(const constant_interval_exprt &o) const;
  tvt less_than_or_equal(const constant_interval_exprt &o) const;
  tvt greater_than_or_equal(const constant_interval_exprt &o) const;
  tvt equal(const constant_interval_exprt &o) const;
  tvt not_equal(const constant_interval_exprt &o) const;

  constant_interval_exprt increment() const;
  constant_interval_exprt decrement() const;

  bool is_empty() const;
  bool is_single_value_interval() const;
  /** END SET OF ARITHMETIC OPERATORS */

  //  tvt contains(constant_interval_exprt &o) const;

  /* SET OF EXPR COMPARATORS */
  static bool equal(const exprt &a, const exprt &b);
  static bool not_equal(const exprt &a, const exprt &b);
  static bool less_than(const exprt &a, const exprt &b);
  static bool less_than_or_equal(const exprt &a, const exprt &b);
  static bool greater_than(const exprt &a, const exprt &b);
  static bool greater_than_or_equal(const exprt &a, const exprt &b);
  /* END SET OF EXPR COMPS */

  /* INTERVAL COMPARISONS, returns tvt.is_true().  False cannot be trusted
   * (could be false or unknown, either use less_than, etc method or use the correct
   * operator)! */
  friend bool operator<(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend bool operator>(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend bool operator<=(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend bool operator>=(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend bool operator==(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend bool operator!=(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);

  /* Operator override for intervals */
  friend const constant_interval_exprt operator+(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator-(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator/(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator*(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator%(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator!(
    const constant_interval_exprt &lhs);
  friend const constant_interval_exprt operator&(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator|(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator^(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator<<(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);
  friend const constant_interval_exprt operator>>(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs);

  friend std::ostream &
  operator<<(std::ostream &out, const constant_interval_exprt &i);
  std::string to_string() const;

  /* Now static equivalents! */
  static tvt is_true(const constant_interval_exprt &a);
  static tvt is_false(const constant_interval_exprt &a);

  static tvt logical_and(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static tvt logical_or(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static tvt logical_xor(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static tvt logical_not(const constant_interval_exprt &a);

  static constant_interval_exprt unary_plus(const constant_interval_exprt &a);
  static constant_interval_exprt unary_minus(const constant_interval_exprt &a);

  /* Binary */
  static constant_interval_exprt
  plus(const constant_interval_exprt &a, const constant_interval_exprt &b);
  static constant_interval_exprt
  minus(const constant_interval_exprt &a, const constant_interval_exprt &b);
  static constant_interval_exprt
  multiply(const constant_interval_exprt &a, const constant_interval_exprt &b);
  static constant_interval_exprt
  divide(const constant_interval_exprt &a, const constant_interval_exprt &b);
  static constant_interval_exprt
  modulo(const constant_interval_exprt &a, const constant_interval_exprt &b);

  /* Binary shifts */
  static constant_interval_exprt left_shift(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static constant_interval_exprt right_shift(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);

  /* Unary bitwise */
  static constant_interval_exprt bitwise_not(const constant_interval_exprt &a);

  /* Binary bitwise */
  static constant_interval_exprt bitwise_xor(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static constant_interval_exprt bitwise_or(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static constant_interval_exprt bitwise_and(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);

  static tvt
  less_than(const constant_interval_exprt &a, const constant_interval_exprt &b);
  static tvt greater_than(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static tvt less_than_or_equal(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static tvt greater_than_or_equal(
    const constant_interval_exprt &a,
    const constant_interval_exprt &b);
  static tvt
  equal(const constant_interval_exprt &a, const constant_interval_exprt &b);
  static tvt
  not_equal(const constant_interval_exprt &a, const constant_interval_exprt &b);

  static constant_interval_exprt increment(const constant_interval_exprt &a);
  static constant_interval_exprt decrement(const constant_interval_exprt &a);

  static bool is_empty(const constant_interval_exprt &a);
  static bool is_single_value_interval(const constant_interval_exprt &a);

  static bool is_top(const constant_interval_exprt &a);
  static bool is_bottom(const constant_interval_exprt &a);

  static bool is_min(const constant_interval_exprt &a);
  static bool is_max(const constant_interval_exprt &a);
  /* End static equivalents */

  bool is_top() const;
  bool is_bottom() const;
  static constant_interval_exprt top(const typet &type);
  static constant_interval_exprt bottom(const typet &type);
  constant_interval_exprt top() const;
  constant_interval_exprt bottom() const;

  bool has_no_lower_bound() const;
  bool has_no_upper_bound() const;
  static bool is_min(const exprt &expr);
  static bool is_max(const exprt &expr);

  /* Generate min and max exprt according to current type */
  min_exprt min() const;
  max_exprt max() const;

  constant_exprt zero() const;
  static constant_exprt zero(const typet &type);
  static constant_exprt zero(const exprt &expr);
  static constant_exprt zero(const constant_interval_exprt &interval);

  /* Private? */
  static constant_interval_exprt get_extremes(
    const constant_interval_exprt &lhs,
    const constant_interval_exprt &rhs,
    const irep_idt &operation);
  static exprt get_extreme(std::vector<exprt> values, bool min = true);
  static exprt get_max(const exprt &a, const exprt &b);
  static exprt get_min(const exprt &a, const exprt &b);
  static exprt get_min(std::vector<exprt> &values);
  static exprt get_max(std::vector<exprt> &values);

  /* we don't simplify in the constructor otherwise */
  static constant_interval_exprt simplified_interval(exprt &l, exprt &r);
  static exprt simplified_expr(exprt expr);

  /* Helpers */
  /* Four common params: self, static: type, expr, interval */

  bool is_numeric() const;
  static bool is_numeric(const typet &type);
  static bool is_numeric(const exprt &expr);
  static bool is_numeric(const constant_interval_exprt &interval);

  bool is_int() const;
  static bool is_int(const typet &type);
  static bool is_int(const exprt &expr);
  static bool is_int(const constant_interval_exprt &interval);

  bool is_float() const;
  static bool is_float(const typet &type);
  static bool is_float(const exprt &expr);
  static bool is_float(const constant_interval_exprt &interval);

  bool is_bitvector() const;
  static bool is_bitvector(const typet &type);
  static bool is_bitvector(const constant_interval_exprt &interval);
  static bool is_bitvector(const exprt &expr);

  bool is_signed() const;
  static bool is_signed(const typet &type);
  static bool is_signed(const exprt &expr);
  static bool is_signed(const constant_interval_exprt &interval);

  bool is_unsigned() const;
  static bool is_unsigned(const typet &type);
  static bool is_unsigned(const exprt &expr);
  static bool is_unsigned(const constant_interval_exprt &interval);

  bool contains_zero() const;
  bool contains(const constant_interval_exprt &interval) const;

  static bool is_extreme(const exprt &expr);
  static bool is_extreme(const exprt &expr1, const exprt &expr2);

  static bool contains_extreme(const exprt expr);
  static bool contains_extreme(const exprt expr1, const exprt expr2);

  bool is_positive() const;
  static bool is_positive(const exprt &expr);
  static bool is_positive(const constant_interval_exprt &interval);

  bool is_zero() const;
  static bool is_zero(const exprt &expr);
  static bool is_zero(const constant_interval_exprt &interval);

  bool is_negative() const;
  static bool is_negative(const exprt &expr);
  static bool is_negative(const constant_interval_exprt &interval);

  static exprt abs(const exprt &expr);

private:
  static void generate_expression(
    const exprt &lhs,
    const exprt &rhs,
    const irep_idt &operation,
    std::vector<exprt> &collection);
  static void append_multiply_expression(
    const exprt &lower,
    const exprt &upper,
    std::vector<exprt> &collection);
  static void append_multiply_expression_max(
    const exprt &expr,
    std::vector<exprt> &collection);
  static void append_multiply_expression_min(
    const exprt &min,
    const exprt &other,
    std::vector<exprt> &collection);
  static exprt generate_division_expression(const exprt &lhs, const exprt &rhs);
  static exprt generate_modulo_expression(const exprt &lhs, const exprt &rhs);
  static exprt generate_shift_expression(
    const exprt &lhs,
    const exprt &rhs,
    const irep_idt &operation);
};

inline const constant_interval_exprt &
to_constant_interval_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_constant_interval);
  return static_cast<const constant_interval_exprt &>(expr);
}

#endif /* SRC_ANALYSES_INTERVAL_H_ */
