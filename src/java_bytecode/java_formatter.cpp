/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_formatter.h"

#include "expr2java.h"

#include <ostream>

std::ostream &java_formattert::format(std::ostream &os, const exprt &expr)
{
  return os << expr2java(expr, ns);
}

std::ostream &java_formattert::format(std::ostream &os, const typet &type)
{
  return os << type2java(type, ns);
}

std::ostream &
java_formattert::format(std::ostream &os, const source_locationt &loc)
{
  return os << loc;
}
