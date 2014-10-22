/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "threeval.h"

const char *tvt::to_string() const
{
  switch(value)
  {
  case TV_TRUE: return "TRUE";
  case TV_FALSE: return "FALSE";
  case TV_UNKNOWN: return "UNKNOWN";
  default: return "ERROR";
  }
}

std::ostream &operator << (std::ostream &out, const tvt &a)
{
  return out << a.to_string();
}
