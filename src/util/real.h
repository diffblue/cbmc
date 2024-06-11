/*******************************************************************\

Module: Real Numbers

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_UTIL_REAL_H
#define CPROVER_UTIL_REAL_H

#include "mp_arith.h"
#include "std_expr.h"

class realt
{
protected:
  // TODO: we will eventually need to move to a list of coefficients (of a
  // polynomial) to be able to represent irrational numbers. See also the
  // KNOWNBUG test cbmc/real-irrational1.
  mp_integer integral, fractional;

public:
  // constructors
  realt() : integral(0), fractional(0)
  {
  }
  realt(const mp_integer &i, const mp_integer &f) : integral(i), fractional(f)
  {
  }
  explicit realt(const mp_integer &i) : realt(i, 0)
  {
  }

  constant_exprt as_expr() const;

  realt &operator-();

  bool operator==(const realt &n) const
  {
    return integral == n.integral && fractional == n.fractional;
  }

  bool operator!=(const realt &n) const
  {
    return integral != n.integral || fractional != n.fractional;
  }

  const mp_integer &get_integral() const
  {
    return integral;
  }

  const mp_integer &get_fractional() const
  {
    return fractional;
  }
};

std::ostream &operator<<(std::ostream &out, const realt &a);

#endif // CPROVER_UTIL_REAL_H
