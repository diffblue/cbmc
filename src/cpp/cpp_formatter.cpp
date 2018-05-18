/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cpp_formatter.h"

#include "expr2cpp.h"

#include <ostream>

std::ostream &cpp_formattert::format(std::ostream &os, const exprt &expr)
{
  return os << expr2cpp(expr, ns);
}

std::ostream &cpp_formattert::format(std::ostream &os, const typet &type)
{
  return os << type2cpp(type, ns);
}

std::ostream &
cpp_formattert::format(std::ostream &os, const source_locationt &loc)
{
  return os << loc;
}
