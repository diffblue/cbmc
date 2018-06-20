/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Container for C-Strings

#include "dstring.h"

#include <ostream>

std::ostream &dstringt::operator<<(std::ostream &out) const
{
  return out << as_string();
}
