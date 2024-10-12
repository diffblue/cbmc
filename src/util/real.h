/*******************************************************************\

Module: Real Numbers

Author: Michael Tautschnig

\*******************************************************************/

#ifndef CPROVER_UTIL_REAL_H
#define CPROVER_UTIL_REAL_H

#include "mp_arith.h"

class realt
{
protected:
  mp_integer integral, fractional;

public:
  // constructors
  realt() : integral(0), fractional(0)
  {
  }
  explicit realt(const mp_integer &i) : integral(i), fractional(0)
  {
  }

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
