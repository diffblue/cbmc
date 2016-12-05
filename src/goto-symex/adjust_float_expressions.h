/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_ADJUST_FLOAT_EXPRESSIONS_H
#define CPROVER_GOTO_SYMEX_ADJUST_FLOAT_EXPRESSIONS_H

#include <util/expr.h>
#include <util/namespace.h>

void adjust_float_expressions(
  exprt &expr,
  const namespacet &ns);

#endif // CPROVER_GOTO_SYMEX_ADJUST_FLOAT_EXPRESSIONS_H
