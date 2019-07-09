/*******************************************************************\

Module: Conversion from Expression or Type to Statement List

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

#include "expr2statement_list.h"

#include <ansi-c/expr2c.h>

std::string expr2stl(const exprt &expr, const namespacet &ns)
{
  // TODO: Implement expr2stl.
  // Expand this section so that it is able to properly convert from
  // CBMC expressions to STL code.
  return expr2c(expr, ns);
}

std::string type2stl(const typet &type, const namespacet &ns)
{
  // TODO: Implement type2stl.
  // Expand this section so that it is able to properly convert from
  // CBMC types to STL code.
  return type2c(type, ns);
}
