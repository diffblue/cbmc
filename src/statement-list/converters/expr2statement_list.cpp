/*******************************************************************\

Module: Conversion from Expression or Type to Statement List

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#include "expr2statement_list.h"

#include <util/symbol.h>

std::string expr2stl(const exprt &expr)
{
  // TODO: Implement expr2stl.
  // Expand this section so that it is able to properly convert from
  // CBMC expressions to STL code.
  return expr.pretty();
}

std::string type2stl(const typet &type)
{
  // TODO: Implement type2stl.
  // Expand this section so that it is able to properly convert from
  // CBMC types to STL code.
  return type.pretty();
}

std::string type2stl(const typet &type, const std::string &identifier)
{
  // TODO: Implement type2stl.
  // Expand this section so that it is able to properly convert from
  // CBMC types to STL code.
  return type.pretty();
}
