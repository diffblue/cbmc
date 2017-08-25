/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_RATIONAL_TOOLS_H
#define CPROVER_UTIL_RATIONAL_TOOLS_H

#include "std_expr.h"

class rationalt;

bool to_rational(const exprt &expr, rationalt &rational_value);
constant_exprt from_rational(const rationalt &rational_value);

#endif // CPROVER_UTIL_RATIONAL_TOOLS_H
