/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Guard Data Structure

#ifndef CPROVER_ANALYSES_GUARD_EXPR_H
#define CPROVER_ANALYSES_GUARD_EXPR_H

#include <iosfwd>

#include <util/std_expr.h>

/// This is unused by this implementation of guards, but can be used by other
/// implementations of the same interface.
struct guard_managert
{
};

class guardt
{
public:
  /// Construct a BDD from an expression
  /// The \c guard_managert parameter is not used, but we keep it for uniformity
  /// with other implementations of guards which may use it.
  explicit guardt(const exprt &e, guard_managert &) : expr(e)
  {
  }

  guardt &operator=(const guardt &other)
  {
    expr = other.expr;
    return *this;
  }

  void add(const exprt &expr);

  void append(const guardt &guard)
  {
    add(guard.as_expr());
  }

  exprt as_expr() const
  {
    return expr;
  }

  void guard_expr(exprt &dest) const;

  bool is_true() const
  {
    return expr.is_true();
  }

  bool is_false() const
  {
    return expr.is_false();
  }

  friend guardt &operator-=(guardt &g1, const guardt &g2);
  friend guardt &operator|=(guardt &g1, const guardt &g2);

private:
  exprt expr;
};

#endif // CPROVER_ANALYSES_GUARD_EXPR_H
