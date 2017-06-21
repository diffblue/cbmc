/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SIMPLIFY_UTILS_H
#define CPROVER_UTIL_SIMPLIFY_UTILS_H

#include "expr.h"

bool sort_operands(exprt::operandst &operands);

bool sort_and_join(exprt &expr);

#endif // CPROVER_UTIL_SIMPLIFY_UTILS_H
