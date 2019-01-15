/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Guard Data Structure

#ifndef CPROVER_UTIL_GUARD_H
#define CPROVER_UTIL_GUARD_H

#include <iosfwd>

#include "std_expr.h"

class guardt
{
public:
  guardt() : expr(true_exprt())
  {
  }

  explicit guardt(const exprt &e) : expr(e)
  {
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

  friend guardt &operator -= (guardt &g1, const guardt &g2);
  friend guardt &operator |= (guardt &g1, const guardt &g2);

private:
  exprt expr;
};

#endif // CPROVER_UTIL_GUARD_H
