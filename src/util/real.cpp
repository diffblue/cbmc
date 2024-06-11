/*******************************************************************\

Module: Real Numbers

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Real Numbers

#include "real.h"

realt &realt::operator-()
{
  integral.negate();
  return *this;
}

std::ostream &operator<<(std::ostream &out, const realt &a)
{
  return out << a.get_integral() << '.' << a.get_fractional();
}
