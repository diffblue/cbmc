/*******************************************************************\

 Module: Interval Predicates

 Author: Daniel Kroening

\*******************************************************************/

#ifndef CPROVER_CPROVER_INTERVAL_EXPR_H
#define CPROVER_CPROVER_INTERVAL_EXPR_H

#include <util/std_expr.h>

/// Shorthand for value>=lower && value<=upper
class in_interval_exprt : public ternary_exprt
{
public:
  in_interval_exprt(exprt value, exprt lower, exprt upper)
    : ternary_exprt(
        "in_interval",
        std::move(value),
        std::move(lower),
        std::move(upper),
        bool_typet())
  {
  }

  and_exprt conjunction() const
  {
    return and_exprt(
      binary_relation_exprt(value(), ID_ge, lower()),
      binary_relation_exprt(value(), ID_le, upper()));
  }

  const exprt value() const
  {
    return op0();
  }

  const exprt lower() const
  {
    return op1();
  }

  const exprt upper() const
  {
    return op2();
  }

  exprt value()
  {
    return op0();
  }

  exprt lower()
  {
    return op1();
  }

  exprt upper()
  {
    return op2();
  }
};

inline const in_interval_exprt &to_in_interval_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == "in_interval");
  return static_cast<const in_interval_exprt &>(expr);
}

inline in_interval_exprt &to_in_interval_expr(exprt &expr)
{
  PRECONDITION(expr.id() == "in_interval");
  return static_cast<in_interval_exprt &>(expr);
}

#endif /* CPROVER_CPROVER_INTERVAL_EXPR_H */
