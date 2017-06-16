/*
 * interval.h
 *
 *  Created on: 16 Jun 2017
 *      Author: dan
 */

#ifndef SRC_ANALYSES_INTERVAL_H_
#define SRC_ANALYSES_INTERVAL_H_

#include <util/expr.h>
#include <util/simplify_expr.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/arith_tools.h>

#include "interval_template.h"

#include <ostream>
#include <sstream>
#include <iostream>

/*
 *
 * Upper set = Specific max (otherwise INF)
 * Lower set = Specific min (otherwise INF)
 */

class max_exprt:public exprt
{
public:
  explicit max_exprt(const typet &_type):
    exprt(ID_max, _type)
  {
  }

  explicit max_exprt(const exprt &_expr):
    exprt(ID_max, _expr.type())
  {
  }
};

class min_exprt:public exprt
{
public:
  explicit min_exprt(const typet &_type):
    exprt(ID_min, _type)
  {
  }

  explicit min_exprt(const exprt &_expr):
    exprt(ID_min, _expr.type())
  {
  }
};



class intervalt
{
public:
  intervalt():
    lower(min_exprt(nil_typet())),
    upper(max_exprt(nil_typet())),
    type(nil_typet())
  {
  }

  explicit intervalt(const exprt &x):
    lower(x),
    upper(x),
    type(x.type())
  {

  }

  intervalt(const typet type_):
    lower(min_exprt(type_)),
    upper(max_exprt(type_)),
    type(type_)
  {
  }

  intervalt(const exprt &l, const exprt &u):
    lower(l),
    upper(u),
    type(calculate_type(l, u))
  {
  }

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
  const intervalt handle_constants(exprt expr) const;
  const intervalt handle_constants(const intervalt &o, exprt expr) const;

  const intervalt eval(const exprt &expr);
  const intervalt eval(const exprt &expr, const intervalt &o);

  /* Unary arithmetic */
  const intervalt unary_plus() const;
  const intervalt unary_minus() const;

  /* Logical */
  const tvt is_true() const;
  const tvt is_false() const;

  const tvt logical_and(const intervalt& o) const;
  const tvt logical_or(const intervalt &o) const;
  const tvt logical_xor(const intervalt &o) const;
  const tvt logical_not() const;

  const intervalt tv_to_interval(const tvt &tv) const;

  /* Binary */
  const intervalt plus(const intervalt &o) const;
  const intervalt minus(const intervalt &o) const;
  const intervalt multiply(const intervalt &o) const;
  const intervalt divide(const intervalt &o) const;
  const intervalt modulo(const intervalt &o) const;

  /* Binary shifts */
  const intervalt left_shift(const intervalt &o) const;
  const intervalt right_shift(const intervalt &o) const;

  /* Unary bitwise */
  const intervalt bitwise_not() const;

  /* Binary bitwise */
  const intervalt bitwise_xor(const intervalt &o) const;
  const intervalt bitwise_or(const intervalt &o) const;
  const intervalt bitwise_and(const intervalt &o) const;

  tvt less_than(const intervalt &o) const;
  tvt greater_than(const intervalt &o) const;
  tvt less_than_or_equal(const intervalt &o) const;
  tvt greater_than_or_equal(const intervalt &o) const;
  tvt equal(const intervalt &o) const;
  tvt not_equal(const intervalt &o) const;

  const intervalt increment() const;
  const intervalt decrement() const;

  bool is_empty() const;
  bool is_constant() const;
  /** END SET OF ARITHMETIC OPERATORS */

//  tvt contains(intervalt &o) const;

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
  friend bool operator< (const intervalt &lhs, const intervalt &rhs);
  friend bool operator> (const intervalt &lhs, const intervalt &rhs);
  friend bool operator<=(const intervalt &lhs, const intervalt &rhs);
  friend bool operator>=(const intervalt &lhs, const intervalt &rhs);
  friend bool operator==(const intervalt &lhs, const intervalt &rhs);
  friend bool operator!=(const intervalt &lhs, const intervalt &rhs);

  /* Operator override for intervals */
  friend const intervalt operator+(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator-(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator/(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator*(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator%(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator!(const intervalt &lhs);
  friend const intervalt operator&(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator|(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator^(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator<<(const intervalt &lhs, const intervalt &rhs);
  friend const intervalt operator>>(const intervalt &lhs, const intervalt &rhs);

  friend std::ostream& operator<< (std::ostream& out, const intervalt &i);
  std::string to_string() const;


  /* Now static equivalents! */
  static const tvt is_true(const intervalt &a);
  static const tvt is_false(const intervalt &a);

  static const tvt logical_and(const intervalt &a, const intervalt &b);
  static const tvt logical_or(const intervalt &a, const intervalt &b);
  static const tvt logical_xor(const intervalt &a, const intervalt &b);
  static const tvt logical_not(const intervalt &a);

  static const intervalt tv_to_interval(const intervalt &interval, const tvt &tv);

  static const intervalt unary_plus(const intervalt &a);
  static const intervalt unary_minus(const intervalt &a);

  /* Binary */
  static const intervalt plus(const intervalt &a, const intervalt &b);
  static const intervalt minus(const intervalt &a, const intervalt &b);
  static const intervalt multiply(const intervalt &a, const intervalt &b);
  static const intervalt divide(const intervalt &a, const intervalt &b);
  static const intervalt modulo(const intervalt &a, const intervalt &b);

  /* Binary shifts */
  static const intervalt left_shift(const intervalt &a, const intervalt &b);
  static const intervalt right_shift(const intervalt &a, const intervalt &b);

  /* Unary bitwise */
  static const intervalt bitwise_not(const intervalt &a);

  /* Binary bitwise */
  static const intervalt bitwise_xor(const intervalt &a, const intervalt &b);
  static const intervalt bitwise_or(const intervalt &a, const intervalt &b);
  static const intervalt bitwise_and(const intervalt &a, const intervalt &b);

  static tvt less_than(const intervalt &a, const intervalt &b);
  static tvt greater_than(const intervalt &a, const intervalt &b);
  static tvt less_than_or_equal(const intervalt &a, const intervalt &b);
  static tvt greater_than_or_equal(const intervalt &a, const intervalt &b);
  static tvt equal(const intervalt &a, const intervalt &b);
  static tvt not_equal(const intervalt &a, const intervalt &b);

  static const intervalt increment(const intervalt &a);
  static const intervalt decrement(const intervalt &a);

  static bool is_empty(const intervalt &a);
  static bool is_constant(const intervalt &a);

  static bool is_top(const intervalt &a);
  static bool is_bottom(const intervalt &a);

  static bool is_min(const intervalt &a);
  static bool is_max(const intervalt &a);
  /* End static equivalents */





  bool is_top() const;
  bool is_bottom() const;
  static const intervalt top(const typet &type);
  static const intervalt bottom(const typet &type);
  const intervalt top() const;
  const intervalt bottom() const;

  bool is_min() const;
  bool is_max() const;
  static bool is_min(const exprt &expr);
  static bool is_max(const exprt &expr);

  /* Generate min and max exprt according to current type */
  min_exprt min() const;
  max_exprt max() const;

  constant_exprt zero() const;
  static constant_exprt zero(const typet &type);
  static constant_exprt zero(const exprt &expr);
  static constant_exprt zero(const intervalt &interval);

  /* Private? */
  static const intervalt get_extremes(const intervalt &lhs, const intervalt &rhs, const exprt operation);
  static exprt get_extreme(std::vector<exprt> values, bool min = true);
  static exprt get_max(const exprt &a, const exprt &b);
  static exprt get_min(const exprt &a, const exprt &b);
  static exprt get_min(std::vector<exprt> &values);
  static exprt get_max(std::vector<exprt> &values);

  /* we don't simplify in the constructor otherwise */
  static const intervalt simplified_interval(exprt &l, exprt &r);
  static exprt simplified_expr(exprt expr);

  /* Don't allow different types in upper and lower */
  const typet& get_type() const;
  const typet& calculate_type(const exprt &l, const exprt &u) const;

  /* Swap lower and upper! */
  const intervalt swap() const;
  static const intervalt swap(intervalt &i);
  /* Helpers */
  /* Four common params: self, static: type, expr, interval */

  bool is_numeric() const;
  static bool is_numeric(const typet &type);
  static bool is_numeric(const exprt &expr);
  static bool is_numeric(const intervalt &interval);

  bool is_int() const;
  static bool is_int(const typet &type);
  static bool is_int(const exprt &expr);
  static bool is_int(const intervalt &interval);

  bool is_float() const;
  static bool is_float(const typet &type);
  static bool is_float(const exprt &expr);
  static bool is_float(const intervalt &interval);

  bool is_bitvector() const;
  static bool is_bitvector(const typet &type);
  static bool is_bitvector(const intervalt &interval);
  static bool is_bitvector(const exprt &expr);

  bool is_signed() const;
  static bool is_signed(const typet &type);
  static bool is_signed(const exprt &expr);
  static bool is_signed(const intervalt &interval);

  bool is_unsigned() const;
  static bool is_unsigned(const typet &type);
  static bool is_unsigned(const exprt &expr);
  static bool is_unsigned(const intervalt &interval);

  bool contains_zero() const;
  bool contains(const intervalt &interval) const;

  static bool is_extreme(const exprt &expr);
  static bool is_extreme(const exprt &expr1, const exprt &expr2);

  static bool contains_extreme(const exprt expr);
  static bool contains_extreme(const exprt expr1, const exprt expr2);

  bool is_positive() const;
  static bool is_positive(const exprt &expr);
  static bool is_positive(const intervalt &interval);

  bool is_zero() const;
  static bool is_zero(const exprt &expr);
  static bool is_zero(const intervalt &interval);

  bool is_negative() const;
  static bool is_negative(const exprt &expr);
  static bool is_negative(const intervalt &interval);

  static exprt abs(const exprt &expr);

private:
  /* This is the entirety */
  const exprt lower;
  const exprt upper;
  const typet type;

  static exprt generate_expression(const exprt &a, const exprt &b, const exprt &operation);
  static exprt generate_multiply_expression(const exprt &a, const exprt &b, exprt operation);
  static exprt generate_multiply_expression_max(const exprt &expr);
  static exprt generate_multiply_expression_min(const exprt &min, const exprt &other);
  static exprt generate_division_expression(const exprt &a, const exprt &b, exprt operation);
  static exprt generate_modulo_expression(const exprt &a, const exprt &b, exprt operation);
  static exprt generate_shift_expression(const exprt &a, const exprt &b, exprt operation);
};

#endif /* SRC_ANALYSES_INTERVAL_H_ */
