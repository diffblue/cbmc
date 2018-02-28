/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_REPLACE_EXPR_H
#define CPROVER_UTIL_REPLACE_EXPR_H

//
// true: did nothing
// false: replaced something
//

#include "expr.h"

#include <unordered_map>

typedef std::unordered_map<exprt, exprt, irep_hash> replace_mapt;

bool replace_expr(const exprt &what, const exprt &by, exprt &dest);
bool replace_expr(const replace_mapt &what, exprt &dest);

#endif // CPROVER_UTIL_REPLACE_EXPR_H
