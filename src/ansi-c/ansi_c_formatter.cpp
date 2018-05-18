/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_formatter.h"

#include "expr2c.h"

#include <ostream>

std::ostream &ansi_c_formattert::format(std::ostream &os, const exprt &expr)
{
  return os << expr2c(expr, ns);
}

std::ostream &ansi_c_formattert::format(std::ostream &os, const typet &type)
{
  return os << type2c(type, ns);
}

std::ostream &
ansi_c_formattert::format(std::ostream &os, const source_locationt &loc)
{
  return os << loc;
}
