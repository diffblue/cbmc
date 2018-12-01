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

class guardt:public exprt
{
public:
  guardt()
  {
    *this = true_exprt();
  }

  guardt &operator=(const exprt &e)
  {
    *this=static_cast<const guardt&>(e);

    return *this;
  }

  void add(const exprt &expr);

  void append(const guardt &guard)
  {
    add(guard);
  }

  exprt as_expr() const
  {
    return *this;
  }

  void guard_expr(exprt &dest) const;

  friend guardt &operator -= (guardt &g1, const guardt &g2);
  friend guardt &operator |= (guardt &g1, const guardt &g2);
};

#endif // CPROVER_UTIL_GUARD_H
