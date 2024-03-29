/*******************************************************************\

Module: Literals

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Literals

#include "literal.h"

#include <ostream>

std::ostream &operator << (std::ostream &out, literalt l)
{
  if(l.is_constant())
    return out << (l.is_true()?"true":"false");
  else
    return out << (l.sign()?"-":"") << l.var_no();
}

std::ostream &operator<<(std::ostream &out, const bvt &bv)
{
  for(auto it = bv.begin(); it != bv.end(); ++it)
  {
    out << *it;
    if(std::next(it) != bv.end())
      out << ' ';
  }
  return out;
}
