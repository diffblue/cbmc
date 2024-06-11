/*******************************************************************\

Module: Real Numbers

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Real Numbers

#include "real.h"

#include "mathematical_types.h"

constant_exprt realt::as_expr() const
{
  std::string d = integer2string(integral);
  if(fractional != 0)
    d += "." + integer2string(fractional);
  return constant_exprt(d, real_typet());
}

realt &realt::operator-()
{
  integral.negate();
  return *this;
}

std::ostream &operator<<(std::ostream &out, const realt &a)
{
  return out << a.get_integral() << '.' << a.get_fractional();
}
