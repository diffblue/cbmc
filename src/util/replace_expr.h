/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_REPLACE_EXPR_H
#define CPROVER_REPLACE_EXPR_H

//
// true: did nothing
// false: replaced something
//

#include "hash_cont.h"
#include "expr.h"

typedef hash_map_cont<exprt, exprt, irep_hash> replace_mapt;

bool replace_expr(const exprt &what, const exprt &by, exprt &dest);
bool replace_expr(const replace_mapt &what, exprt &dest);

#endif
