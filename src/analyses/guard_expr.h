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
struct guard_expr_managert
{
};

class guard_exprt
{
public:
  /// Construct a BDD from an expression
  /// The \c guard_managert parameter is not used, but we keep it for uniformity
  /// with other implementations of guards which may use it.
  explicit guard_exprt(const exprt &e, guard_expr_managert &) : expr(e)
  {
  }

  guard_exprt &operator=(const guard_exprt &other)
  {
    expr = other.expr;
    return *this;
  }

  void add(const exprt &expr);

  void append(const guard_exprt &guard)
  {
    add(guard.as_expr());
  }

  exprt as_expr() const
  {
    return expr;
  }

  /// The result of \ref as_expr is not always in a simplified form
  /// and may requires some simplification.
  /// This can vary according to the guard implementation.
  static constexpr bool is_always_simplified = false;

  DEPRECATED(SINCE(2019, 08, 21, "use implies instead"))
  exprt guard_expr(exprt expr) const;

  /// Return `guard => other` or a simplified variant thereof if either guard or
  /// dest are trivial.
  guard_exprt implies(const guard_exprt &other) const;

  bool is_true() const
  {
    return expr.is_true();
  }

  bool is_false() const
  {
    return expr.is_false();
  }

  friend guard_exprt &operator-=(guard_exprt &g1, const guard_exprt &g2);
  friend guard_exprt &operator|=(guard_exprt &g1, const guard_exprt &g2);

  /// Underlying representation of the guard. The type can vary for each guard
  /// implementation.
  const exprt &underlying() const
  {
    return expr;
  }

private:
  exprt expr;
};

#endif // CPROVER_ANALYSES_GUARD_EXPR_H
